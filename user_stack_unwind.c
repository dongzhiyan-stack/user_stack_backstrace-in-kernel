#include <linux/tick.h>
#include <linux/stddef.h>
#include <linux/unistd.h>
#include <linux/export.h>
#include <linux/ptrace.h>
#include <linux/sys.h>
#include <linux/user.h>
#include <linux/init.h>
#include <linux/completion.h>
#include <linux/kallsyms.h>
#include <linux/random.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/mm.h>
#include <linux/mman.h>
#include <linux/signal.h>
#include <linux/binfmts.h>
#include <linux/string.h>
#include <linux/file.h>
#include <linux/slab.h>
#include <linux/elfcore.h>
#include <linux/init.h>
#include <linux/highuid.h>
#include <linux/compiler.h>
#include <linux/highmem.h>
#include <linux/pagemap.h>
#include <linux/vmalloc.h>
#include <linux/security.h>
#include <linux/random.h>
#include <linux/elf.h>
#include <linux/utsname.h>
#include <linux/coredump.h>
#include <linux/sched.h>
#include <asm/uaccess.h>
#include <asm/param.h>
#include <asm/page.h>
#include <asm/stacktrace.h>

#ifdef CONFIG_MIPS
#include <asm/asm.h>
#include <asm/mipsregs.h>
#include <asm/processor.h>
#include <asm/uaccess.h>
#include <asm/io.h>
#include <asm/inst.h>
#endif
/*
目前有三个问题需要研究
1 文件系统，为什么/lib/lib-glibc.so 只能在user_stack_backstrace_open/read,在其他函数open read就会返回错误码，跟踪在内核文件系统哪里导致的,这是个很好的内核开发过程!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

2 arm64 dump_stack 现在的测试程序，test_a 休眠后，对这个线程栈回溯，打印user_unwind_frame get_user1 error fp:0x7ff74960f0，明明 maps文件显示cat /proc/205/maps 7ff7476000--7ff7497000 rwxp 00000000 00:00 0 【stack】明明0x7ff74960f0在这个范围内，但是打印显示，无法从这片用户空间及栈所属区复制数据，需要跟踪get_user失败的原因，这是个很好的内核开发过程!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
3  mips架构 _send_signal函数，不能调用user_stack_backstrace函数，读文件有调度，提示禁止调度，arm64没有这个问题。基本确定是发送信号这个系统调用，禁止了内核抢占，就是在内核态无法调度了，读文件过程当然会有休眠，这个问题其实解决起来，就是从禁止抢占入手，又是个很好的内核开发过程!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
*/


#define NAME_LEN 50
struct Sym_Fun_Info{
    char name[NAME_LEN];
	unsigned long fun_first_instruct_addr;
	unsigned long fun_end_instruct_addr;
};
struct User_Stack_Unwind{
    unsigned long sys_info_size;
	unsigned long elf_text_start;
	unsigned long elf_text_end;
	unsigned long thread_stack_start;
    struct list_head sym_head;
    struct Sym_Fun_Info sym_info;
	struct task_struct * thread;
};
struct Sym_Info{
    char name[NAME_LEN];
    unsigned long fun_first_instruct_addr;//函数指令首地址
	struct list_head sym_list;
	unsigned long fun_end_instruct_addr;//函数指令结束地址
};

struct mips_frame_info {
	void		*func;
	unsigned long	func_size;
	int		frame_size;
	int		pc_offset;
};
struct Elf_Lib_Info{
    struct elf_shdr section_dynsym;//保存elf文件的 dynsym section结构体
	struct elf_shdr section_dynstr;//保存elf文件的 dynstr section结构体
	struct elf_shdr section_symtab;//保存elf文件的 symtab section结构体
	
	struct elf_sym *first_lib_sym;//指向elf文件dynsym section数据区，该数据区是一个个库函数的struct elf_sym结构体，elf可执行程序和lib库文件都用到
	unsigned char *elf_lib_fun_str;//指向elf文件dynstr section的数据区，该数据区是一个个库函数名字字符串，elf可执行程序和lib库文件都用到
	struct elf_sym *first_elf_sym;//保存elf 可执行程序文件中.symtab section区数据，该数据区是一个个可执行程序自己的函数的struct elf_sym结构体
	unsigned char *elf_fun_str;//保存elf 可执行程序文件中.strtab section区数据，该数据区是一个个可执行程序函数名字字符串
	
	unsigned long *got_addr;//保存got段的内存首地址
	unsigned long  elf_lib_fun_off;//库函数原始函数地址与实际运行地址的偏差
	int used;
};

static struct Elf_Lib_Info elf_lib_info,lib_info;
static struct User_Stack_Unwind user_stack_unwind;

static int print_user_ip_sym(unsigned long pc);
static char *get_elflib_path_file_name(struct task_struct *task,unsigned long addr);
static long get_file_size(struct file *file);
static int get_lib_fun_offset(struct Elf_Lib_Info *elf_lib_info,struct Elf_Lib_Info *lib_info);
static int get_lib_fun_info(struct Sym_Fun_Info * sym_lib_info,struct Elf_Lib_Info *lib_info,unsigned long addr,unsigned long lib_fun_offset);
static int get_elf_fun_info(struct Sym_Fun_Info * elf_sym_info,struct Elf_Lib_Info *elf_info,unsigned long addr);

#define READ_ELF_PART

#ifdef CONFIG_MIPS
#define elf_sym elf32_sym

#define J_TARGET(pc,target)	\
		(((unsigned long)(pc) & 0xf0000000) | ((target) << 2))

static inline int is_ra_save_ins(union mips_instruction *ip)
{
#ifdef CONFIG_CPU_MICROMIPS
	union mips_instruction mmi;

	/*
	 * swsp ra,offset
	 * swm16 reglist,offset(sp)
	 * swm32 reglist,offset(sp)
	 * sw32 ra,offset(sp)
	 * jradiussp - NOT SUPPORTED
	 *
	 * microMIPS is way more fun...
	 */
	if (mm_insn_16bit(ip->halfword[0])) {
		mmi.word = (ip->halfword[0] << 16);
		return ((mmi.mm16_r5_format.opcode == mm_swsp16_op &&
			 mmi.mm16_r5_format.rt == 31) ||
			(mmi.mm16_m_format.opcode == mm_pool16c_op &&
			 mmi.mm16_m_format.func == mm_swm16_op));
	}
	else {
		mmi.halfword[0] = ip->halfword[1];
		mmi.halfword[1] = ip->halfword[0];
		return ((mmi.mm_m_format.opcode == mm_pool32b_op &&
			 mmi.mm_m_format.rd > 9 &&
			 mmi.mm_m_format.base == 29 &&
			 mmi.mm_m_format.func == mm_swm32_func) ||
			(mmi.i_format.opcode == mm_sw32_op &&
			 mmi.i_format.rs == 29 &&
			 mmi.i_format.rt == 31));
	}
#else
	/* sw / sd $ra, offset($sp) */
	return (ip->i_format.opcode == sw_op || ip->i_format.opcode == sd_op) &&
		ip->i_format.rs == 29 &&
		ip->i_format.rt == 31;
#endif
}

static inline int is_jump_ins(union mips_instruction *ip)
{
#ifdef CONFIG_CPU_MICROMIPS
	/*
	 * jr16,jrc,jalr16,jalr16
	 * jal
	 * jalr/jr,jalr.hb/jr.hb,jalrs,jalrs.hb
	 * jraddiusp - NOT SUPPORTED
	 *
	 * microMIPS is kind of more fun...
	 */
	union mips_instruction mmi;

	mmi.word = (ip->halfword[0] << 16);

	if ((mmi.mm16_r5_format.opcode == mm_pool16c_op &&
	    (mmi.mm16_r5_format.rt & mm_jr16_op) == mm_jr16_op) ||
	    ip->j_format.opcode == mm_jal32_op)
		return 1;
	if (ip->r_format.opcode != mm_pool32a_op ||
			ip->r_format.func != mm_pool32axf_op)
		return 0;
	return (((ip->u_format.uimmediate >> 6) & mm_jalr_op) == mm_jalr_op);
#else
	if (ip->j_format.opcode == j_op)
		return 1;
	if (ip->j_format.opcode == jal_op)
		return 1;
	if (ip->r_format.opcode != spec_op)
		return 0;
	return ip->r_format.func == jalr_op || ip->r_format.func == jr_op;
#endif
}

static inline int is_sp_move_ins(union mips_instruction *ip)
{
#ifdef CONFIG_CPU_MICROMIPS
	/*
	 * addiusp -imm
	 * addius5 sp,-imm
	 * addiu32 sp,sp,-imm
	 * jradiussp - NOT SUPPORTED
	 *
	 * microMIPS is not more fun...
	 */
	if (mm_insn_16bit(ip->halfword[0])) {
		union mips_instruction mmi;

		mmi.word = (ip->halfword[0] << 16);
		return ((mmi.mm16_r3_format.opcode == mm_pool16d_op &&
			 mmi.mm16_r3_format.simmediate && mm_addiusp_func) ||
			(mmi.mm16_r5_format.opcode == mm_pool16d_op &&
			 mmi.mm16_r5_format.rt == 29));
	}
	return (ip->mm_i_format.opcode == mm_addiu32_op &&
		 ip->mm_i_format.rt == 29 && ip->mm_i_format.rs == 29);
#else
	/* addiu/daddiu sp,sp,-imm */
	if (ip->i_format.rs != 29 || ip->i_format.rt != 29)
		return 0;
	if (ip->i_format.opcode == addiu_op || ip->i_format.opcode == daddiu_op)
		return 1;
#endif
	return 0;
}
/**
* user_process_lookup_size_offset - 根据传入的指令地址计算所处函数的指令字节数和该指令地址的偏移
* @addr - 传入的指令地址
* @symbolsize - 根据addr计算出的
* @offset - addr相对函数指令首地址的偏移
*
* returns:
*     1：找到addr所处的函数
*     0: 没有找到addr所处的函数 
*/
static int user_process_lookup_size_offset(unsigned long addr, unsigned long *symbolsize,unsigned long *offset)
{
	struct Sym_Fun_Info sym_func_info;
    int ret;

    //如果addr在可执行程序代码段
    if(addr >= user_stack_unwind.elf_text_start && addr <= user_stack_unwind.elf_text_end)
	{
        ret = get_elf_fun_info(&sym_func_info,&elf_lib_info,addr);
	    if(ret)
	    {
	        printk(KERN_ERR"%s get_elf_fun_info:%d error\n",__func__,ret);
	        return 0;
	    }
	}
	else//addr在库中
	{
	    //根据可执行程序的.dynstr和.dynsym信息分析出库函数的运行地址和库函数原始的偏差值
	    ret = get_lib_fun_offset(&elf_lib_info,&lib_info);
	    if(ret)
	    {
	        printk(KERN_ERR"%s get_lib_fun_offset:%d error\n",__func__,ret);
	        return 0;
	    }
		memset(&sym_func_info,0,sizeof(struct Sym_Fun_Info));
	    //根据addr获取库函数所处的函数首地址、函数指令字节数等信息
        ret = get_lib_fun_info(&sym_func_info,&lib_info,addr,elf_lib_info.elf_lib_fun_off);
	    if(ret)
	    {
			/*mips架构double free栈回溯时，中途会遇到未知C库函数。比如test_a ->C库未知函数1->C库未知函数2->abort->raise。
			栈回溯时，abort->raise两个函数都能打印出来，但是回溯到未知函数2，就会终止，arm64用gdb栈回溯也是这样，直接终止调。
			但是我的arm64内核double free栈回溯能完整回溯，这是比gdb优越的另一点。由于mips栈回溯依赖每个函数的指令首地址，现在
			碰到C库未知函数2，当然不知道该函数名字和指令首地址，那就直接return 0栈回溯结束，这就从原理上证实，mips架构double free
			栈回溯存在问题，有时间研究一下"C库未知函数2"出现的原因。
			*/
	        printk(KERN_ERR"%s get_lib_fun_info:%d error\n",__func__,ret);
	        return 0;
	    }
	}
	
	*offset = addr - sym_func_info.fun_first_instruct_addr;
    *symbolsize = sym_func_info.fun_end_instruct_addr - sym_func_info.fun_first_instruct_addr;
	
	return 1;
}
/**
* get_frame_info - 根据传入的函数指令首地址，依次分析汇编指令，根据汇编指令找到函数栈大小和函数返回地址在栈中的保存位置
* @info - info->func就是函数指令首地址，info->frame_size保存函数栈大小，info->pc_offset保存函数返回地址保存在函数栈中的偏移
*
* returns:
*    0：分析汇编指令后，找到函数栈大小和函数返回地址在栈中的保存位置
*    1：没有根据汇编指令分析出函数函数返回地址在栈中的保存位置
*   <0：其他异常
*/
static int get_frame_info(struct mips_frame_info *info)
{
#ifdef CONFIG_CPU_MICROMIPS
	union mips_instruction *ip = (void *) (((char *) info->func) - 1);
#else
	union mips_instruction *ip = info->func;
#endif

    union mips_instruction *tmp_ip = ip;
    union mips_instruction ip_data;
    unsigned long tmp_data;
	unsigned long *p_ip;

	unsigned max_insns = info->func_size / sizeof(union mips_instruction);
	unsigned i;

	info->pc_offset = -1;
	info->frame_size = 0;

	if (!ip)
		goto err;

	if (max_insns == 0)
		max_insns = 128U;	/* unknown function size */
	max_insns = min(128U, max_insns);

	for (i = 0; i < max_insns; i++, ip++) {
	    //保留原ip值，下方恢复ip值
        tmp_ip = ip;
        //union mips_instruction 结构大小为unsigned long,一条指令占的空间大小
	    p_ip = (unsigned long*)ip;
	    if(get_user(tmp_data,p_ip))
	    {
	        printk(KERN_ERR"%s get_user error ip:0x%p\n",__func__,ip);
	        return -EFAULT;
	    }
	    memcpy(&ip_data,&tmp_data,sizeof(union mips_instruction));
	    ip = &ip_data;
       
        if (is_jump_ins(ip))
			break;
		if (!info->frame_size) {
			if (is_sp_move_ins(ip))
			{
#ifdef CONFIG_CPU_MICROMIPS
				if (mm_insn_16bit(ip->halfword[0]))
				{
					unsigned short tmp;

					if (ip->halfword[0] & mm_addiusp_func)
					{
						tmp = (((ip->halfword[0] >> 1) & 0x1ff) << 2);
						info->frame_size = -(signed short)(tmp | ((tmp & 0x100) ? 0xfe00 : 0));
					} else {
						info->frame_size = -(signed short)(tmp & 0xf);
					}
					ip = (void *) &ip->halfword[1];
					ip--;
				} else
#endif
				info->frame_size = - ip->i_format.simmediate;
			}
		    ip = tmp_ip;
			continue;
		}
		if (info->pc_offset == -1 && is_ra_save_ins(ip)) {
			info->pc_offset =
				ip->i_format.simmediate / sizeof(long);
			break;
		}
        //恢复原ip值，目的是不破坏函数原有框架
		ip = tmp_ip;
	}
	if (info->frame_size && info->pc_offset >= 0) /* nested */
		return 0;
	if (info->pc_offset < 0) /* leaf */
		return 1;
	/* prologue seems boggus... */
	printk(KERN_ERR"%s error end\n",__func__);
err:
	return -1;
}
/** user_unwind_stack_by_address - 根据当前函数的pc值，计算出上一级函数的栈顶地址和当前函数的返回地址
* @stack_page - 函数内核栈顶
* @*sp - 保存上一级函数栈顶
* @pc - 当前函数的pc值，就是栈回溯过程打印的函数地址
* @*ra - 崩溃函数中没有调用其他函数时，是应用段错误当时的ra寄存数据，这种情况第一次栈回溯时使用
*
* returns:
*    >0：找到当前函数返回地址，就是上一级函数中的指令地址
*     0: 没有找到当前函数返回地址
*/
static unsigned long  user_unwind_stack_by_address(unsigned long stack_page,
					      unsigned long *sp,
					      unsigned long pc,
					      unsigned long *ra)
{
	struct mips_frame_info info;
	unsigned long size, ofs;
	int leaf;
	extern void ret_from_irq(void);
	extern void ret_from_exception(void);
	if (!stack_page)
		return 0;

	/*
	 * If we reached the bottom of interrupt context,
	 * return saved pc in pt_regs.
	 */	 
	 //question2/////////////////////////////////////////////////////////////这不是针对用户空间的限制，我得参考其他地方修改i这里，先注释掉
#if 0
	if (pc == (unsigned long)ret_from_irq ||
	    pc == (unsigned long)ret_from_exception) {
		struct pt_regs *regs;
		if (*sp >= stack_page &&
		    *sp + sizeof(*regs) <= stack_page + THREAD_SIZE - 32) {
			regs = (struct pt_regs *)*sp;
			pc = regs->cp0_epc;
			if (__kernel_text_address(pc)) {
				*sp = regs->regs[29];
				*ra = regs->regs[31];
				return pc;
			}
		}
		return 0;
	}
#endif

	if (!user_process_lookup_size_offset(pc, &size, &ofs))
	{
	    printk(KERN_ERR"%s can not find vaild user function at pc:0x%lx\n",__func__,pc);
		return 0;
	}
	/*
	 * Return ra if an exception occurred at the first instruction
	 */
	if (unlikely(ofs == 0)) {
		pc = *ra;
		*ra = 0;
		return pc;
	}

	info.func = (void *)(pc - ofs);
	info.func_size = ofs;	/* analyze from start to ofs */
	leaf = get_frame_info(&info);
	if (leaf < 0)
		return 0;

	//question 6这是对栈空间的限制，我需要把限制应用栈空间的代码加上，是否可以先分析出该应用应用层栈空见的范围，然后这里判断合法性
	/*
	if (*sp < stack_page ||
	    *sp + info.frame_size > stack_page + THREAD_SIZE - 32)
		return 0;
    */
    //判断sp是否超出当前进程的用户空间栈底
	if(*sp + info.frame_size > user_stack_unwind.thread_stack_start)
	{
	    printk("%s expand user thread stack\n",__func__);
		return 0;
	}
	/*
	!!!!!!!!!!!!!!!!!!!核心理解!!!!!!!!!!!!!!!!!!!!!!!!
	应用崩溃在库函数里，这个if是关键。以test_a执行memcpy为例，先执行memcpy@plt函数，注意这个memcpy@plt是编译链接是自动生成，跟test_a函数在一起，反汇编就能看到，是执行实际库函数的跳板。这个函数的指令首地址是0x4013b0，test_a函数指令首地址是0x400858,在memcpy@plt函数中指令内存中，从0x411408内存地址获取c库的memcpy的指令首地址0x779b4910，readelf -a dump_stack看PLT GOT段内容，再结合反回编的汇编代码看看。然后程序就跳转到0x779b4910内存单元执行真实的C库函数memcpy，0x779b4910就在C库函数的maps的指令段。注意，注意，这个跳转过程没有看到addiu sp,sp.-152指令分配栈空间的指令，也没有看到sw ra,148(sp)把函数返回地址保存到函数栈最后的指令。相当于库函数memcpy的执行情况跟我测试的test_a_一样，没有执行其他函数，就不会分配栈空间和保存ra值到栈中,实际观察memcpy汇编代码，确实没有执行其他函数。所以memcpy函数中崩溃了，就直接使用ra寄存器的值了，ra就是memcpy的函数返回地址，就是test_a函数指令中调用memcpy@plt函数那条指令的下一条指令地址，之后就返回test_a函数了。C库好多函数都没有addiu sp,sp,-152和sw ra,148(sp)类似指令，分析这些函数得注意，这些函数中就没有调用其他函数，只能使用ra寄存器的值，推算该函数的返回地址。
	*/
	if (leaf)
    {
		/*
		 * For some extreme cases, get_frame_info() can
		 * consider wrongly a nested function as a leaf
		 * one. In that cases avoid to return always the
		 * same value.
		 */

//本质是:这个ra是个内核态指针，它指向内核变量struct pt_regs结构体里的ra1变量，值是0x7fff0000，是个用户空间的指令地址，现在要得到ra1变量的数据0x7fff0000，*ra就行了，因为ra指针指向ra1，*ra就是指针指向的变量内存里的数据
	    pc = pc != *ra ? *ra : 0;
    }
	else
	{
		//pc = ((unsigned long *)(*sp))[info.pc_offset];
		unsigned long *tmp;
		tmp = (unsigned long *)(*sp) + info.pc_offset;
        if(get_user(pc,tmp))
		{
		    printk(KERN_ERR"%s  get_user sp info.pc_offset  error\n",__func__);
		    return 0;
		}
	}	
    //这里有点绕，上层函数是把栈变量sp的地址传进来，这里是sp指针指向这个栈变量，*p才表示栈变量自己，这个栈变量增加info.frame_size，自加即可。C语言的变量增加3，变量自己+=3即可，这点说起来有点弱智，但是指针指向变量后意味深长
	//有一个理解上的很大误区，sp指向栈空间，*sp不就是对指针指向的栈空间赋值???????没传过来弯道.*p就是操作指针指向的空间
	*sp += info.frame_size;
    *ra = 0; 

	return pc;
}
/** user_unwind_stack - 根据当前函数的pc值，计算出上一级函数的栈顶地址和当前函数的返回地址
* @task - 当前进程task结构
* @*sp - 保存上一级函数栈顶
* @pc - 当前函数的pc值，就是栈回溯过程打印的函数地址
* @*ra - 崩溃函数中没有调用其他函数时，是应用段错误当时的ra寄存数据，这种情况第一次栈回溯时使用
*
* returns:
*    >0：找到当前函数返回地址，就是上一级函数中的指令地址
*     0: 没有找到当前函数返回地址
*/
static unsigned long user_unwind_stack(struct task_struct *task, unsigned long *sp,unsigned long pc, unsigned long *ra)
{
    unsigned long stack_page = (unsigned long)task_stack_page(task);

    return user_unwind_stack_by_address(stack_page, sp, pc, ra);
}
/** show_user_backtrace - mips架构栈回溯的核心，在该函数计算和打印栈回溯的各级函数信息
* @task - 当前进程task结构
* @regs - 异常进程的struct pt_regs结构，包含栈回溯过程需要的pc、ra、sp等寄存器
*
*  returns:void
*/
static void show_user_backtrace(struct task_struct *task, const struct pt_regs *regs)
{
	unsigned long sp = regs->regs[29];
	unsigned long ra = regs->regs[31];
	unsigned long pc = regs->cp0_epc;
    unsigned long where;
	if (!task)
		task = user_stack_unwind.thread;
////question! 3 最好是判断pc是否是用户空间指令//////////////////////////////////////////////////////////////////////////////////////		
/*
	if (raw_show_trace || !__kernel_text_address(pc)) {
		show_raw_backtrace(sp);
		return;
	}
*/
	printk("Call Trace:\n");
	do {
	     where = pc;
		 pc = user_unwind_stack(task, &sp, pc, &ra);
         print_user_ip_sym(where);
	} while (pc);
	printk("\n");
}

#elif defined CONFIG_ARM64

#define elf_sym elf64_sym
/** instructions_belong_to_one_fun - 判断pc1和pc2两个指令地址是否处于同一个函数
* @pc1 - 函数指令地址1
* @pc2 - 函数指令地址2
*
* returns:
*     1：pc1和pc2两个指令地址处于同一个函数
*     0：pc1和pc2两个指令地址不处于同一个函数
*/
static int instructions_belong_to_one_fun(struct Elf_Lib_Info *elf_info,unsigned long pc1,unsigned long pc2)
{    
    struct elf_sym *elf_fun_sym;
    int i;
	
	elf_fun_sym = (struct elf_sym*)elf_info->first_elf_sym;

    //这里只判断pc1和pc2是否处于同一个可执行程序函数的情况，不判断是否处于同一个动态库函数的情况
    for(i = 0;i < elf_info->section_symtab.sh_size/sizeof(struct elf_sym);i++)
	{
        //elf_fun_sym->st_value 是lib库文件中每个库函数的默认函数首地址，elf_fun_sym->st_value + lib_fun_offset 是库函数重定向后的函数首地址
	    if((pc1 >= elf_fun_sym->st_value) && (pc1 < elf_fun_sym->st_value + elf_fun_sym->st_size))
		{
			if((pc2 >= elf_fun_sym->st_value) && (pc2 < elf_fun_sym->st_value + elf_fun_sym->st_size))
				return 1;
		}
		elf_fun_sym ++;
	}
	return 0;
}
/** user_unwind_frame - arm64架构从当前函数栈中分析出当前函数返回地址和和上一级函数栈的地址
* @frame->sp 保存上一级函数栈顶
* @frame->fp 保存上一级函数的栈的第二片内存地址
* @frame->pc 保存当前函数的返回地址
* 
* returns:
*     0：获取frame结构成员成功
*    <0：获取frame结构成员失败
*/
static int user_unwind_frame(struct stackframe *frame)
{
    unsigned long high, low;
    unsigned long fp = frame->fp;

    low = frame->sp;
    high = ALIGN(low, THREAD_SIZE);

	/////question 9 这是arm64架构用于判断内核栈是否超出空间，我要修改成判断应用程序栈是否超出空间//////
    /*if (fp < low || fp > high || fp & 0xf)
    return -EINVAL;*/

    frame->sp = fp + 0x10;
    //frame->fp = *(unsigned long *)(fp);
    //从用户空间获取上一级函数的栈的第二片内存地址
    if(get_user(frame->fp, (unsigned long *)(fp)))
	{
	    printk(KERN_ERR"%s get_user1 error fp:0x%lx\n",__func__,fp);
	    return -EFAULT;
	}
    //frame->pc = *(unsigned long *)(fp + 8);
    //从用户空间获取崩溃函数的返回地址
    if(get_user(frame->pc, (unsigned long *)(fp + 8)))
	{
	    printk(KERN_ERR"%s get_user2 error fp:0x%lx\n",__func__,fp);
	    return -EFAULT;
    }
    return 0;
}
/** show_user_backtrace - arm64栈回溯的核心，在该函数计算和打印栈回溯的各级函数信息
* @task - 当前进程task结构
* @regs - 异常进程的struct pt_regs结构，包含栈回溯过程需要的pc、sp、fp等寄存器
*
*  returns:void
*/
static void show_user_backtrace(struct task_struct *task, const struct pt_regs *regs)
{
    struct stackframe frame;
    int ret,cycle_count;
    unsigned long where;
    unsigned long second_fun;
#ifdef READ_ELF_PART
    struct Sym_Fun_Info sym_func_info;
#endif
	frame.fp = regs->regs[29];
    frame.sp = regs->sp;
    frame.pc = regs->pc;

    if(get_user(second_fun, (unsigned long *)(regs->regs[29] + 8)))
	{
	    printk(KERN_ERR"%s get_user error fp:0x%llx sp:0x%llx\n",__func__,regs->regs[29]+8,regs->sp);
	    return;
    }

	cycle_count = 0;
    while (1)
    {
	   /*这里的if判断用于崩溃函数test_a_没有调用其他函数的情况，正常函数lr寄存器数据和函数栈第二片内存中的数据是一致的，崩溃函数没有调用其他函数时，开始开头指令没有把lr和fp寄存器入栈，此时的fp寄存器regs->regs[29]保存的数据还是上一级函数栈的第二片内存地址，则第一片内存地址中的数据一定是再上一级的函数地址，此时与lr寄存器regs->regs[30]肯定不想等，就是下边的second_fun != regs->regs[30]。lr寄存器只要有函数调用，就保存函数返回地址。有个特例，如果崩溃函数有调用其他函数，但是崩溃位置在函数调用后，比如test_a_函数调用了printf后崩溃了，此时lr寄存器数据是printf("22")的下一条指令地址，就是lr还保持执行printf函数时的状态，看来lr寄存器的数据只在函数调用时被修改，在函数返回后不会恢复。这种情况second_fun != regs->regs[30]也成立，就是靠second_fun != regs->regs[30]函数，判断出regs->pc 和 regs->regs[30]指向的指令地址不属于同一个函数的，就可以过滤这种情况了。
	   void test_a_()
	   {
	       int *p =NULL;
	       printf("22");
           *p = 0;
	   }
	   */
        where = frame.pc;
		if((0 == cycle_count)&& (task == current) &&  (second_fun != regs->regs[30]) && (0 == instructions_belong_to_one_fun(&elf_lib_info,regs->regs[30],regs->pc)))
		{
		    frame.pc = regs->regs[30];
		}
		else
		{
            //获取函数的返回地址存于frame.pc和上一级函数的栈的第二片内存地址存于frame.fp
            ret = user_unwind_frame(&frame);
            if (ret < 0)
                break;
		}
		
		//在可执行程序代码段
		if(where >= user_stack_unwind.elf_text_start && where < user_stack_unwind.elf_text_end)
		{   //根据addr获取可执行程序的函数的首地址、函数指令字节数等信息，保存到user_stack_unwind.sym_info结构
			ret = get_elf_fun_info(&sym_func_info,&elf_lib_info,where);
			if(ret)
			{
				printk(KERN_ERR"%s get_elf_fun_info:%d error\n",__func__,ret);
				return;
			}
		}
		else//在库函数代码段
		{
		    //根据可执行程序文件和lib库文件的.dynstr和.dynsym信息分析出库函数的运行地址和库函数原始的偏差值
	        ret = get_lib_fun_offset(&elf_lib_info,&lib_info);
	        if(ret)
			{
			    printk(KERN_ERR"%s get_lib_fun_offset:%d error\n",__func__,ret);
	            return;
		    }
		    memset(&sym_func_info,0,sizeof(struct Sym_Fun_Info));
	        //根据addr获取库函数所处的函数首地址、函数指令字节数等信息，保存到user_stack_unwind.sym_info结构
            ret = get_lib_fun_info(&sym_func_info,&lib_info,where,elf_lib_info.elf_lib_fun_off);
	        if(ret)
			{
				/*
				arm64 double free过程，test_a ->C库未知函数1->C库未知函数2->abort->raise，在回溯到C库未知函数2时，
				就找不到C库函数，此时get_lib_fun_info返回-1，但是不出错返回，继续栈回溯，最后能完整回溯到可执行程序代码段，gdb做不到。
				arm64栈回溯使用fp寄存器定位函数栈，不依赖函数函数指令首地址，所以遇到未知C库函数，照样能栈回溯。
				*/
				printk(KERN_ERR"%s get_lib_fun_info:%d error\n",__func__,ret);
	           //return 0;
			}
		}
		cycle_count ++;

        print_user_ip_sym(where); 
    }
}
#else
    #error "unsupport architecture!!!!!!"
#endif


/** print_user_ip_sym - 打印pc所处函数的名字及相对函数指令首地址的偏移等信息
* @pc - 栈回溯过程每一级函数的指令地址
* 
* returns:
*     1：找到pc所处的函数
*     0：没有找到pc所处的函数
*/
static int  print_user_ip_sym(unsigned long pc)
{
	unsigned int fun_size,pc_off;
    struct Sym_Fun_Info *sym_info;

    fun_size = 0;
	
   //user_stack_unwind.sym_info 保存库函数的指令信息，新的改造，也保存可执行程序的自身函数信息
    sym_info = &user_stack_unwind.sym_info;
    if(!fun_size && (pc >= sym_info->fun_first_instruct_addr && pc <= sym_info->fun_end_instruct_addr))
	{
	    fun_size = sym_info->fun_end_instruct_addr - sym_info->fun_first_instruct_addr;
		pc_off = pc - sym_info->fun_first_instruct_addr;
	#ifdef CONFIG_ARM64	
        printk(KERN_ALERT"<0x%010lx> %s() 0x%x/0x%x\n",pc,sym_info->name,pc_off,fun_size);
	#else
		printk(KERN_ALERT"<0x%08lx> %s() 0x%x/0x%x\n",pc,sym_info->name,pc_off,fun_size);
    #endif		
		memset(sym_info,0x00,sizeof(struct Sym_Fun_Info));
		return 1;
	}
	
	if(!fun_size)
	{
	    printk(KERN_ERR"cat not find valid user function\n");
	}
	return 0;
}
/** read_elf_section_info - 读取elf可执行程序和库文件的 .dynsym .dynstr .plt .got.plt section的数据保存到struct Elf_Lib_Info *elf_info结构，
* @elf_file - elf可执行程序和库文件的struct file结构
* @elf_info - 该结构体成员保存elf文件的.dynsym .dynstr .plt .got.plt section的数据
* @is_elf_file - 1:elf可执行程序 0:elf库文件
*
* returns:
*     0：读取elf文件的.dynsym .dynstr .plt .got.plt section的数据成功
*    <0：读取失败
*/
static int read_elf_section_info(struct file *elf_file,struct Elf_Lib_Info *elf_info,int is_elf_file)
{
   // struct elf_shdr *section_head;
	struct elf_shdr *p_section = NULL;
	char *section_name;
	int i;
	long retval;
    struct elfhdr elf_head;
	unsigned char *section_data = NULL;

    //读取elf文件头
	retval = kernel_read(elf_file,0,(unsigned char *)&elf_head,sizeof(struct elfhdr));
	if (retval <= 0) {
		retval = -EIO;
		goto err;
	}
	section_data = kmalloc(sizeof(struct elf_shdr)*elf_head.e_shnum,GFP_KERNEL);
	if(!section_data)
	{
		retval = -ENOMEM;
		printk(KERN_ERR"%s kmalloc fail 1\n",__func__);
		goto err;
	}
	//读取所有section结构体信息到section_data数组
	retval = kernel_read(elf_file,elf_head.e_shoff,section_data,sizeof(struct elf_shdr)*elf_head.e_shnum);
	if (retval <= 0) {
		retval = -EIO;
		goto err;
	}
	//p_section 指向第一个section首地址
	p_section = (struct elf_shdr *)section_data;
	//section指向编号是elf_head->e_shstrndx的section，这个section对应的数据是每个section的名字字符串集合
	p_section += elf_head.e_shstrndx;
	section_name = kmalloc(p_section->sh_size,GFP_KERNEL);
	if(!section_name)
	{
		retval = -ENOMEM;
		printk(KERN_ERR"%s kmalloc fail 2\n",__func__);
		goto err;
	}
	
	//section_name 指向编号是elf_head->e_shstrndx的section的数据区首地址，这个section的数据各个section的名字字符串。p_section->sh_offset是该section对应的数据的偏移
    retval = kernel_read(elf_file,p_section->sh_offset,section_name,p_section->sh_size);
	if (retval <= 0) {
		printk("%s line:%d kernel_read fail\n",__func__,__LINE__);
		retval = -EIO;
		goto err;
	}
	  //指向第一个section结构
	  p_section = (struct elf_shdr *)section_data;
	  for(i = 0;i < elf_head.e_shnum;i++)
	  {
	      //.dynsym 段
		  if(/*SHT_SYMTAB == p_section->sh_type && */strcmp(".dynsym",&section_name[p_section->sh_name]) == 0)
		  {
		  #ifdef CONFIG_ARM64
			  printk("%s find ,section sh_offset:0x%llx sh_size:0x%llx\n",&section_name[p_section->sh_name],p_section->sh_offset,p_section->sh_size);
		  #else
			  printk("%s find ,section sh_offset:0x%x sh_size:0x%x\n",&section_name[p_section->sh_name],p_section->sh_offset,p_section->sh_size);
		  #endif
			  memcpy(&elf_info->section_dynsym,p_section,sizeof(struct elf_shdr));//保存.dynstr 段的信息
			  elf_info->first_lib_sym = kmalloc(p_section->sh_size,GFP_KERNEL);//
			  if(!elf_info->first_lib_sym)
                  goto err;
			  //从dynsym段指定的文件偏移地址复制dynsym段的数据到 elf_lib_info.first_lib_sym，这些数据就是struct elf_sym结构的集合，每一个struct elf32_sym结构代表一个库函数信息，包括该库函数名字符串索引、库函数默认运行地址、库函数指令字节数
			  //memcpy((void *)elf_lib_info->first_lib_sym,(unsigned char *)elf_head + p_section->sh_offset,p_section->sh_size);
                retval = kernel_read(elf_file,p_section->sh_offset,(unsigned char *)elf_info->first_lib_sym,p_section->sh_size);
				if (retval <= 0) {
					printk("%s line:%d kernel_read fail d\n",__func__,__LINE__);
					retval = -EIO;
					goto err;
				}			  
		  }
          //.dynstr 段
		  else if(/*SHT_STRTAB == p_section->sh_type && */strcmp(".dynstr",&section_name[p_section->sh_name]) == 0)
		  {
		   #ifdef CONFIG_ARM64
			  printk("%s find ,section sh_offset:0x%llx sh_size:0x%llx\n",&section_name[p_section->sh_name],p_section->sh_offset,p_section->sh_size);
		   #else
			  printk("%s find ,section sh_offset:0x%x sh_size:0x%x\n",&section_name[p_section->sh_name],p_section->sh_offset,p_section->sh_size);
		   #endif
			  memcpy(&elf_info->section_dynstr,p_section,sizeof(struct elf_shdr));//保存.dynstr 段section结构
			  elf_info->elf_lib_fun_str = kmalloc(p_section->sh_size,GFP_KERNEL);//
			  if(!elf_info->elf_lib_fun_str)
                  goto err;
			  //从dynstr段指定的文件偏移地址复制库函数字符串数据到 elf_info->elf_lib_fun_str
			  //memcpy((void *)elf_lib_info->elf_lib_fun_str,(unsigned char *)elf_head + p_section->sh_offset,p_section->sh_size);
                retval = kernel_read(elf_file,p_section->sh_offset,elf_info->elf_lib_fun_str,p_section->sh_size);
				if (retval <= 0) {
					printk("%s line:%d kernel_read fail d\n",__func__,__LINE__);
					retval = -EIO;
					goto err;
				}
		  }
		  //.plt段，plt段是库函数跳转表，我们执行的printf库函数，是先跳转到这个段的printf@GLIBC_2.0 函数，然后跳转到got段函数表，这里是每个库函数的重定向后的函数指针，在这里运行到c库真实的printf函数
		  else if(/*SHT_STRTAB == p_section->sh_type && */strcmp(".plt",&section_name[p_section->sh_name]) == 0)
		  {
		   #ifdef CONFIG_ARM64
		      printk("%s find ,section sh_addr:0x%llx sh_offset:0x%llx sh_size:0x%llx\n",&section_name[p_section->sh_name],p_section->sh_addr,p_section->sh_offset,p_section->sh_size);
		   #else
		      printk("%s find ,section sh_addr:0x%x sh_offset:0x%x sh_size:0x%x\n",&section_name[p_section->sh_name],p_section->sh_addr,p_section->sh_offset,p_section->sh_size);
		   #endif
		  }
		  //.got段，该段的sh_addr成员是程序运行后got段的用户空间内存地址，这片内存的数据是plt段库函数的重定向后库函数地址，真实库函数地址
		  else if(/*SHT_STRTAB == p_section->sh_type && */strcmp(".got.plt",&section_name[p_section->sh_name]) == 0)
		  {
		   #ifdef CONFIG_ARM64
		      printk("%s find  sh_addr:0x%llx\n",&section_name[p_section->sh_name],p_section->sh_addr);
		   #else
		      printk("%s find  sh_addr:0x%x\n",&section_name[p_section->sh_name],p_section->sh_addr);
		   #endif
		      elf_info->got_addr = (unsigned long *)p_section->sh_addr;
		  }
		  
		  //是elf可执行程序
		  if(is_elf_file)
		  {
			//.symtab 段，可执行程序自己的函数的一个个 elf_sym 结构
			if(/*SHT_SYMTAB == p_section->sh_type && */strcmp(".symtab",&section_name[p_section->sh_name]) == 0)
			{
           #ifdef CONFIG_ARM64
			  printk("%s find ,section sh_offset:0x%llx sh_size:0x%llx\n",&section_name[p_section->sh_name],p_section->sh_offset,p_section->sh_size);
		  #else
			  printk("%s find ,section sh_offset:0x%x sh_size:0x%x\n",&section_name[p_section->sh_name],p_section->sh_offset,p_section->sh_size);
		  #endif 
              memcpy(&elf_info->section_symtab,p_section,sizeof(struct elf_shdr));//保存.symtab 段section结构
			  elf_info->first_elf_sym = kmalloc(p_section->sh_size,GFP_KERNEL);//
			  if(!elf_info->first_elf_sym)
                  goto err;
			  //从.symtab段指定的文件偏移地址读取.symtab段的数据到 elf_info->first_elf_sym,，这些数据就是struct elf_sym结构的集合，每一个struct elf32_sym结构代表一个函数信息，包括该库函数名字符串索引、库函数默认运行地址、库函数指令字节数
                retval = kernel_read(elf_file,p_section->sh_offset,(unsigned char *)elf_info->first_elf_sym,p_section->sh_size);
				if (retval <= 0) {
					printk("%s line:%d kernel_read fail d\n",__func__,__LINE__);
					retval = -EIO;
					goto err;
				}			       
			}
			//.strtab 段，可执行程序自己的函数名字字符串存储在这里
			else if(/*SHT_STRTAB == p_section->sh_type && */strcmp(".strtab",&section_name[p_section->sh_name]) == 0)
			{
		   #ifdef CONFIG_ARM64
			  printk("%s find ,section sh_offset:0x%llx sh_size:0x%llx\n",&section_name[p_section->sh_name],p_section->sh_offset,p_section->sh_size);
		   #else
			  printk("%s find ,section sh_offset:0x%x sh_size:0x%x\n",&section_name[p_section->sh_name],p_section->sh_offset,p_section->sh_size);
		   #endif
			  elf_info->elf_fun_str = kmalloc(p_section->sh_size,GFP_KERNEL);//
			  if(!elf_info->elf_fun_str)
                  goto err;
			  //从.strtab段指定的文件偏移地址读取函数字符串数据到 elf_info->elf_fun_str
                retval = kernel_read(elf_file,p_section->sh_offset,elf_info->elf_fun_str,p_section->sh_size);
				if (retval <= 0) {
					printk("%s line:%d kernel_read fail d\n",__func__,__LINE__);
					retval = -EIO;
					goto err;
				}
			}
		  }
		  p_section++;		  
	  }
	  
      elf_info->used = 1;
	  
    retval = 0;
err:
    if(section_data)
		kfree(section_data);
    return retval;
}
/** get_lib_fun_offset - 计算库函数的实际运行首地址和原始首地址之差保存到 elf_lib_info->elf_lib_fun_off
* @elf_lib_info - 可执行程序的struct Elf_Lib_Info 结构
* @lib_info - 库文件的struct Elf_Lib_Info 结构
*
* returns:
*     0:计算出库函数的实际运行首地址和原始首地址之差
*    <0:没有计算库函数的实际运行首地址和原始首地址之差
*
*  note：根据可执行程序的got段内存中存储的库函数strcmp运行地址got_lib_fun_val(假设got段第四片内存保存的数据是strcmp库函数的运行地址，got_lib_fun_val保存这个运行地址)，然后在lib库文件中，.dynstr段搜索函数名字字符串是"strcmp"的函数，而.dynsym段保存的数据————函数struct elf_sym结构与 .dynstr段的函数名字字符串也是一一对应的。
   比如， 假如.dynstr 段的第一个函数名字字符串是 "strcmp"， .dynsym段的第一个struct elf_sym结构就是strcmp库函数的，该结构的st_value是strcmp库函数的俄原始地址，st_size是库函数的指令字节数。
   知道了strcmp库函数的运行地址got_lib_fun_val，又在lib库文件中.dynstr段找到了strcmp的字符串，同样的偏移找到了 .dynsym段strcmp库函数的struct elf_sym结构，就知道了它的原始函数地址st_value。got_lib_fun_val-st_value就是库函数的运行地址和原始地址的差值off，应该适用于所有库函数。之后我知道一个库函数的st_value，就知道了它的运行地址首地址st_value+off，函数指令结束地址end，那知道任何一个库函数中的崩溃地址pc， pc > st_value+off并且 pc < end时，就知道崩溃库函数指令pc处于哪个库函数了，当然也知道它的名字字符串。
   有一点需要注意，库函数的运行地址和原始地址的低12位数据是一样的，测试证实了这一点，我觉得这与PAGE_SIZE是2的12次方有关。
*/
static int get_lib_fun_offset(struct Elf_Lib_Info *elf_lib_info,struct Elf_Lib_Info *lib_info)
{
    struct elf_sym *elf_lib_sym,*lib_sym;
    //section_dynstr first_lib_sym;
    unsigned char *lib_fun_name,*elf_lib_fun_name;
    unsigned long *p_got_lib_fun;
    unsigned long  got_lib_fun_val = 0;
    int i;
    int ret = -1;
    
	if(elf_lib_info->elf_lib_fun_off)
	{
	    printk(KERN_DEBUG"%s  elf_lib_fun_off already ok\n",__func__);
		return 0;
	}

	//可执行程序的
	elf_lib_sym = (struct elf_sym*)elf_lib_info->first_lib_sym;
	elf_lib_fun_name = (char *)elf_lib_info->elf_lib_fun_str;
    p_got_lib_fun = (unsigned long *)elf_lib_info->got_addr;//这个是用户态的地址，要用get_user复制数据
#ifdef CONFIG_MIPS	
    p_got_lib_fun += 2;//函数指针偏移到第4片内存，前几片内存存储的是got段相关信息，第4片内存开始存储的数据才是库函数的首地址数据
	//elf_lib_sym指向的第4片内存，因为readelf观察mips架构elf文件的.dynsym段，发现前三个struct elf_sym分别是 空、_DYNAMIC_LINKING _ITM_deregisterTMCloneTab，第4个才是可执行程序有效的库函数elf_sym
	/*现在做了限制，只有是FUNC属性的elf_sym，got.plt段的p_got_lib_fun指针才偏移,elf_lib_sym就不用++了*/
    //elf_lib_sym += 2;
#else 
    p_got_lib_fun += 3;
	//elf_lib_sym += 2;
#endif

    //库文件的
    lib_sym = (struct elf_sym *)lib_info->first_lib_sym;
    lib_fun_name = (char *)lib_info->elf_lib_fun_str;

        //elf_lib_info->section_dynsym.sh_size 是elf库文件.dynsym段总大小，除以struct elf_sym大小，就是库函数总数，一个函数信息用一个struct elf_sym结构表示
    for(i = 0;i < elf_lib_info->section_dynsym.sh_size/sizeof(struct elf_sym);i++)
	{
        //从用户空间的got段内存复制库函数的首地址到got_lib_fun_val，这个地址是重定向后的地址，真实的库函数指令首地址
	    if(get_user(got_lib_fun_val,p_got_lib_fun))
	    {
	        printk(KERN_ERR"%s get_user error  0x%p\n",__func__,p_got_lib_fun);
	        return -EFAULT;
	    }
		printk(KERN_DEBUG"   %s got_lib_fun_val:0x%lx p_got_lib_fun:0x%p %s\n",__func__,got_lib_fun_val,p_got_lib_fun,&elf_lib_fun_name[elf_lib_sym->st_name]);

#ifdef CONFIG_MIPS
        //mips 按照观察，库函数的运行地址大于0x70000000，这个不太正规，????????????????????????????????????????????????????????????????????????question 8????????????????????????????????????
		if((got_lib_fun_val > 0x70000000) && (STT_FUNC == ELF_ST_TYPE(elf_lib_sym->st_info)))
#elif defined CONFIG_ARM64
//加上STT_FUNC限制，必须是func类型，测试发现_ITM_deregisterTMCIoneTab函数干扰，但是他的属性是NOTYPE，他也是.dynsym段的成员
		if((got_lib_fun_val > 0x7000000000) && (STT_FUNC == ELF_ST_TYPE(elf_lib_sym->st_info)))
#else
   #error "not support !!!!!"
#endif
		{
		    printk(KERN_DEBUG"!!!%s elf_lib_info find %s got_lib_fun_val:0x%lx p_got_lib_fun:0x%p\n",__func__,&elf_lib_fun_name[elf_lib_sym->st_name],got_lib_fun_val,p_got_lib_fun);
			//指向.plt.got区下一片内存地址，.plt.got区的内存地址，amr64从第四片内存开始，都是库函数的运行地址，假设所有库函数都运行过了。而可执行程序文件的.dynsym区除了库函数，还有NOTIFY属性的干扰。所以elf_lib_sym++每次都执行，p_got_lib_fun++只有是有效库函数时才执行。
		    //p_got_lib_fun++;//指向下一个库函数首指令地址所在内存
		}
		if(STT_FUNC == ELF_ST_TYPE(elf_lib_sym->st_info))
			p_got_lib_fun++;//指向下一个库函数首指令地址所在内存

		elf_lib_sym ++;//指向像一个库函数 struct elf_sym 结构
	}
	
	
	elf_lib_sym = (struct elf_sym*)elf_lib_info->first_lib_sym;
	elf_lib_fun_name = (char *)elf_lib_info->elf_lib_fun_str;
    p_got_lib_fun = (unsigned long *)elf_lib_info->got_addr;//这个是用户态的地址，要用get_user复制数据
#ifdef CONFIG_MIPS	
    p_got_lib_fun += 2;
#else 
    p_got_lib_fun += 3;
#endif

    //elf_lib_info->section_dynsym.sh_size 是elf库文件.dynsym段总大小，除以struct elf_sym大小，就是库函数总数，一个函数信息用一个struct elf_sym结构表示
    for(i = 0;i < elf_lib_info->section_dynsym.sh_size/sizeof(struct elf_sym);i++)
	{
        //从用户空间的got段内存复制库函数的首地址到got_lib_fun_val，这个地址是重定向后的地址，真实的库函数指令首地址
	    if(get_user(got_lib_fun_val,p_got_lib_fun))
	    {
	        printk(KERN_ERR"%s get_user error  0x%p\n",__func__,p_got_lib_fun);
	        return -EFAULT;
	    }
        
		//printk(KERN_DEBUG"%s got_lib_fun_val:0x%lx p_got_lib_fun:0x%p %s\n",__func__,got_lib_fun_val,p_got_lib_fun,&elf_lib_fun_name[elf_lib_sym->st_name]);

#ifdef CONFIG_MIPS
        //mips 按照观察，库函数的运行地址大于0x70000000，这个不太正规，????????????????????????????????????????????????????question 8????????????????????????????????????
		if((got_lib_fun_val > 0x70000000) && (STT_FUNC == ELF_ST_TYPE(elf_lib_sym->st_info)))
#elif defined CONFIG_ARM64
//加上STT_FUNC限制，必须是func类型，测试发现_ITM_deregisterTMCIoneTab函数干扰，但是他的属性是NOTYPE，他也是.dynsym段的成员
		if((got_lib_fun_val > 0x7000000000) && (STT_FUNC == ELF_ST_TYPE(elf_lib_sym->st_info)))
#else
   #error "not support !!!!!"
#endif
		{
		    printk(KERN_DEBUG"%s elf_lib_info find %s got_lib_fun_val:0x%lx\n",__func__,&elf_lib_fun_name[elf_lib_sym->st_name],got_lib_fun_val);
			//p_got_lib_fun++;//指向下一个库函数首指令地址所在内存
			break;
		}
		
		if(STT_FUNC == ELF_ST_TYPE(elf_lib_sym->st_info))
			p_got_lib_fun++;//指向下一个库函数首指令地址所在内存
		
		elf_lib_sym ++;//指向像一个库函数struct elf_sym结构
		
	}

    //此时elf_lib_sym指向的可执行程序中的.dynsym段用到的库函数的struct elf_sym结构，got_lib_fun_val是该库函数的
	//运行指令首地址，&elf_lib_fun_name[elf_lib_sym->st_name]就是该库函名字符串

	/*在库文件中的.dynstr段和.dynsym段分析与 &elf_lib_fun_name[elf_lib_sym->st_name] 库函数名字字符串一致的
	库函数，找到它的struct elf_sym *lib_sym结构，取出它的st_value就是库函数的原始地址，与got_lib_fun_val的
	差值就是库函数的运行地址与原始地址的偏差*/

	for(i = 0;i < lib_info->section_dynsym.sh_size/sizeof(struct elf_sym);i++)
	{
	    if(0  == strcmp(&elf_lib_fun_name[elf_lib_sym->st_name],&lib_fun_name[lib_sym->st_name]))
        {
		    elf_lib_info->elf_lib_fun_off = got_lib_fun_val - lib_sym->st_value;

		#ifdef CONFIG_ARM64
		    printk(KERN_DEBUG"%s lib_info find %s st_value:0x%llx elf_lib_fun_off:0x%lx\n",__func__,&lib_fun_name[lib_sym->st_name],lib_sym->st_value,elf_lib_info->elf_lib_fun_off);
		#else
		    printk(KERN_DEBUG"%s lib_info find %s st_value:0x%x elf_lib_fun_off:0x%lx\n",__func__,&lib_fun_name[lib_sym->st_name],lib_sym->st_value,elf_lib_info->elf_lib_fun_off);
		#endif
		 
             ret =0;
		     break;
		}

		lib_sym++;
	}

    if(0 != ret)
	    printk(KERN_ERR"%s cat not find match lib fun name from elf_lib_sym\n",__func__);
	return ret;
}
/** get_lib_fun_info - 根据addr计算出它所处于的库函数的名字、函数运行首地址、函数运行结束地址
* @sym_lib_info - 保存库函数的名字、函数运行首地址、函数运行结束地址
* @lib_info - 该结构体成员主要包含elf库文件的 dynsym、dynstr section数据的首地址
* @addr - 栈回溯过程的函数地址
* @lib_fun_offset - 库函数的运行首地址和结束地址之差
*
* returns:
*    0: 根据addr计算出它所处于的库函数
*   <0: 没有找到addr所处的库函数
*/
static int get_lib_fun_info(struct Sym_Fun_Info * sym_lib_info,struct Elf_Lib_Info *lib_info,unsigned long addr,unsigned long lib_fun_offset)
{
    struct elf_sym *lib_sym;
    unsigned char *lib_fun_name;
    int i;
	int ret = -1;

	lib_sym = (struct elf_sym*)lib_info->first_lib_sym;
    lib_fun_name = (char *)lib_info->elf_lib_fun_str;

    //elf_lib_info->section_dynsym.sh_size 是elf库文件.dynsym段总大小，除以struct elf_sym大小，就是库函数总数，一个函数信息用一个struct elf_sym结构表示
    for(i = 0;i < lib_info->section_dynsym.sh_size/sizeof(struct elf_sym);i++)
	{
        //lib_sym->st_value 是lib库文件中每个库函数的默认函数首地址，lib_sym->st_value + lib_fun_offset 是库函数重定向后的函数首地址
	    if((addr >= lib_sym->st_value + lib_fun_offset) && (addr < lib_sym->st_value + lib_fun_offset + lib_sym->st_size))
		{
		    //lib_fun_name 是库函数名字字符串首地址，elf_lib_sym->st_name是当前函数名字字符串在lib_fun_name数组的索引
		    strncpy(sym_lib_info->name,&lib_fun_name[lib_sym->st_name],NAME_LEN);
            sym_lib_info->fun_first_instruct_addr = lib_sym->st_value + lib_fun_offset;//库函数指令首地址
			sym_lib_info->fun_end_instruct_addr = lib_sym->st_value + lib_fun_offset + lib_sym->st_size;//库函数指令结束地址
            memcpy(&user_stack_unwind.sym_info,sym_lib_info,sizeof(struct Sym_Fun_Info));

      #ifdef CONFIG_ARM64
			printk(KERN_DEBUG"%s find %s first_fun_addr:0x%lx size:0x%llx  st_value:0x%llx\n",__func__,sym_lib_info->name,sym_lib_info->fun_first_instruct_addr,lib_sym->st_size,lib_sym->st_value);
	  #else		
			printk(KERN_DEBUG"%s find %s first_fun_addr:0x%lx size:0x%x  st_value:0x%x\n",__func__,sym_lib_info->name,sym_lib_info->fun_first_instruct_addr,lib_sym->st_size,lib_sym->st_value);
	  #endif
	        /*测试证实，double free栈回溯时，第一级函数是gsignal或者raise，这两个函数的st_value和st_size完全一样，就是两个不同的函数
			名字，但是对应同一个函数。但是gsignal会先搜索到，gdb此时栈回溯时打印的是raise函数，所以这里就不直接return 0，而是一直搜索，
			使用最后找到的库函数*/
	        ret = 0;
            //return 0;
         }

		lib_sym ++;//指向下一个库函数struct elf_sym结构
	}
	return ret;
}
/** get_elf_fun_info - 根据addr计算出它所处于的可执行程序中的函数名字、函数运行首地址、函数运行结束地址
* @sym_lib_info - 保存函数的名字、函数运行首地址、函数运行结束地址
* @lib_info - 该结构体成员主要包含elf可执行程序文件的 dynsym、dynstr section数据的首地址
* @addr - 栈回溯过程的函数地址
*
* returns:
*    0: 根据addr计算出它所处于的函数
*   <0: 没有找到addr所处的函数
*/
static int get_elf_fun_info(struct Sym_Fun_Info * elf_sym_info,struct Elf_Lib_Info *elf_info,unsigned long addr)
{
    struct elf_sym *elf_fun_sym;
    unsigned char *elf_fun_name;
    int i;
    int ret = -1;
	
	elf_fun_sym = (struct elf_sym*)elf_info->first_elf_sym;
    elf_fun_name = (char *)elf_info->elf_fun_str;

    //elf_lib_info->section_dynsym.sh_size 是elf库文件.dynsym段总大小，除以struct elf_sym大小，就是库函数总数，一个函数信息用一个struct elf_sym结构表示
    for(i = 0;i < elf_info->section_symtab.sh_size/sizeof(struct elf_sym);i++)
	{
        //elf_fun_sym->st_value 是lib库文件中每个库函数的默认函数首地址，elf_fun_sym->st_value + lib_fun_offset 是库函数重定向后的函数首地址
	    if((addr >= elf_fun_sym->st_value) && (addr < elf_fun_sym->st_value + elf_fun_sym->st_size))
		{
		    //elf_fun_name 是库函数名字字符串首地址，elf_lib_sym->st_name是当前函数名字字符串在lib_fun_name数组的索引
		    strncpy(elf_sym_info->name,&elf_fun_name[elf_fun_sym->st_name],NAME_LEN);
            elf_sym_info->fun_first_instruct_addr = elf_fun_sym->st_value;//库函数指令首地址
			elf_sym_info->fun_end_instruct_addr = elf_fun_sym->st_value + elf_fun_sym->st_size;//库函数指令结束地址
            memcpy(&user_stack_unwind.sym_info,elf_sym_info,sizeof(struct Sym_Fun_Info));

      #ifdef CONFIG_ARM64
			printk(KERN_DEBUG"%s find %s first_fun_addr:0x%lx size:0x%llx  st_value:0x%llx\n",__func__,elf_sym_info->name,elf_sym_info->fun_first_instruct_addr,elf_fun_sym->st_size,elf_fun_sym->st_value);
	  #else		
			printk(KERN_DEBUG"%s find %s first_fun_addr:0x%lx size:0x%x  st_value:0x%x\n",__func__,elf_sym_info->name,elf_sym_info->fun_first_instruct_addr,elf_fun_sym->st_size,elf_fun_sym->st_value);
	  #endif
	        ret = 0;
            //return 0;
        }

		elf_fun_sym ++;//指向下一个库函数struct elf_sym结构
	}
	return ret;
}
/** get_elflib_path_file_name - 根据传入的addr这个某个库函数指令地址计算出属于哪个库文件的
* @task - 当前栈回溯进程
* @addr - 与栈回溯有关的某个库函数指令地址
*
* returns：
*     NULL:没有找到与addr构成文件映射的库文件
*     其他:与addr构成文件映射的库文件名字字符串
*/
static char *get_elflib_path_file_name(struct task_struct *task,unsigned long addr)
{
    struct vm_area_struct *vma;
	char buf[50];
    char *filename;
    //基本原理是，根据传入的addr在进程vma链表里搜索，找到地址符合的vma
    vma = find_vma(task->mm,addr);
	if(NULL == vma)
	{
	    printk(KERN_ERR"cat not find valid elf_lib file at addr:0x%lx\n",addr);
	    return NULL;
	}
	if(vma && vma->vm_file)	
	{//filename = d_path(&file->f_path, name_curpos, remaining);
		filename = d_path(&vma->vm_file->f_path,buf, sizeof(buf));
		printk("elflib file path: %s \n",filename);
		return  filename;
	}
    return NULL;
}
/** get_elf_path_file - 得到异常可执行程序的文件名字
* @task - 栈回溯进程的task结构
* @text_start - 可执行程序代码段首地址
* @text_end - 可执行程序代码段结束地址
*
* returns:
*    NULL:没有找到可执行程序文件
*    其他:可执行程序的文件名称
*/
static char *get_elf_path_file(struct task_struct *task,unsigned long *text_start,unsigned long *text_end)
{
    struct vm_area_struct *vma;
	struct mm_struct *mm;
    //struct file *file = vma->vm_file;
    char buf[50];
    char *filename;

	mm = get_task_mm(task);
	if(!mm)
	    return NULL;
	//for (vma = mm->mmap; vma; vma = vma->vm_next)
	//进程的用户空间vma链表挂在mm->mmap起始的vma里，第一个vma我觉得应该是进程elf文件路径
	vma = mm->mmap;
    if(vma && vma->vm_file)
	{//filename = d_path(&file->f_path, name_curpos, remaining);
	    filename = d_path(&vma->vm_file->f_path,buf, sizeof(buf));
	    printk("elf file path: %s \n",filename);
		//可执行程序的代码段起始地址和结束地址，这个vma是可执行程序应用空间的第一个vma，第一个vma就是text段
		*text_start = vma->vm_start;
		*text_end   = vma->vm_end;
	    return  filename;
	}

    return NULL;
}
/** get_file_size - 内核态得到文件大小
* @file - 文件的struct file结构
*
* returns:
*      -1:获取文件大小失败
*    其他:文件大小
*/
static  long get_file_size(struct file *file)
{
	struct kstat st;
	if (vfs_getattr(&file->f_path, &st))
  	    return -1;
	if (!S_ISREG(st.mode))
		return -1;
	if (st.size != (long)st.size)
		return -1;
	return st.size;
}
/** user_stack_backstrace - 内核对异常应用栈回溯的入口函数
* @regs - 栈回溯进程当时的struct pt_regs结构
* @task - 栈回溯进程的结构
*
* returns:
*    0:栈回溯过程没有报错
*   <0:栈回溯过程发生报错
*/
int user_stack_backstrace(struct pt_regs *regs,struct task_struct *task)
{
    char elf_path_name[100],lib_path_name[100];
	int retval = 0;
    unsigned long text_start,text_end;
    unsigned long addr;
    mm_segment_t oldfs;
    struct file *elf_file = NULL;
	struct file *lib_file = NULL;

    printk(KERN_ALERT"user thread:%s  pid:%d  stack strace\n",current->comm,current->pid);
    
    strncpy(elf_path_name,get_elf_path_file(current,&text_start,&text_end),sizeof(elf_path_name));
	if(elf_path_name[0] == '\0')
	{
	    printk(KERN_ERR"cat not find elf path file\n");
		retval = -ENOEXEC;
	    goto err;
	}

	memset(&user_stack_unwind,0,sizeof(struct User_Stack_Unwind));
	memset(&elf_lib_info,0,sizeof(struct Elf_Lib_Info));
	memset(&lib_info,0,sizeof(struct Elf_Lib_Info));
	
    user_stack_unwind.elf_text_start = text_start;
    user_stack_unwind.elf_text_end   = text_end;
    user_stack_unwind.thread_stack_start = task->mm->start_stack;
    user_stack_unwind.thread = task;

    oldfs = get_fs();
	set_fs(KERNEL_DS);

    elf_file = open_exec(elf_path_name);
    retval = PTR_ERR(elf_file);
    if (IS_ERR(elf_file))
	{
	    printk(KERN_ERR"open elf file:%s fail\n",elf_path_name);
		retval = -ENOEXEC;
		goto err;
	}
    printk("%s size:%ld\n",elf_path_name,get_file_size(elf_file));
	
#ifdef CONFIG_MIPS
    addr = regs->cp0_epc;
#else
    addr = regs->pc;
#endif
  
    //崩溃地址在库中
    if(addr > user_stack_unwind.elf_text_end)
    {
		strncpy(lib_path_name,get_elflib_path_file_name(user_stack_unwind.thread,addr),sizeof(lib_path_name));
        lib_file = open_exec(lib_path_name);
        retval = PTR_ERR(lib_file);
        if (IS_ERR(lib_file))
	    {
	        printk(KERN_ERR"open lib file:%s fail\n",lib_path_name);
		    retval = -ENOEXEC;
		    goto err;
	    }
	    //获取动态库的symtab、dynsym、dynstr、symstr、plt、got.plt等section的数据
		retval = read_elf_section_info(lib_file,&lib_info,0);
		if(retval)
		{
		   goto err;
		}
    }
  
    //获取可执行程序的symtab、dynsym、dynstr、symstr、plt、got.plt等section的数据
	retval = read_elf_section_info(elf_file,&elf_lib_info,1);
    if(retval)
    {
	   goto err;
    }

    set_fs(oldfs);
		

	show_user_backtrace(current,regs);
	
	retval = 0;
err:
	
	if(elf_lib_info.first_lib_sym)
		kfree(elf_lib_info.first_lib_sym);
	if(elf_lib_info.elf_lib_fun_str)
		kfree(elf_lib_info.elf_lib_fun_str);
	if(elf_lib_info.first_elf_sym)
		kfree(elf_lib_info.first_elf_sym);
	if(elf_lib_info.elf_fun_str)
		kfree(elf_lib_info.elf_fun_str);
	
	if(lib_info.first_lib_sym)
		kfree(lib_info.first_lib_sym);
	if(lib_info.elf_lib_fun_str)
		kfree(lib_info.elf_lib_fun_str);
	
	////////////////////////question 7 这里没有file_close操作，内核也找不到，仔细找找
	if (elf_file)
		fput(elf_file);
	if (lib_file)
		fput(lib_file);
   //question 6////////////////////////////////错误码跟内核统一，不要只有-1，用内核的错误码retval = -ENOEXEC	  
   return retval;
}
EXPORT_SYMBOL(user_stack_backstrace);
