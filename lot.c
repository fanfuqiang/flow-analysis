/*------------------------------------------------------------------------
implememtation the linker's O3 optimzation
	just some simple control flow analysis and data flow analysis
------------------------------------------------------------------------*/

#include "stdhdr.h"
#include "libgputils.h"
#include "gplink.h"
//#include "lot.h"
#define KF_CORE_SIZE 4096

//#define MAXSIZE 4*1024
typedef struct  hex_block_t  hex_block;
typedef struct block_link_t {
	hex_block *ft;		/*from or to*/
	struct block_link_t *next;
} block_link;

struct hex_block_t {
	unsigned int begin;	//begin index of MemBlock
	unsigned int end;	//
	block_link *fore;
	block_link *succ;
	hex_block *next;
	enum bank_no entry_blkno;	//entry block number, 0 or 1
	enum bank_no exit_blkno;	//entry block number, 0 or 1
	short visited;
	short visting;				//this odd member used to de-circle, do you have any idea better?
};

enum bank_no {bank_0 = 1, bank_1, bank_init = 0, bank_undef = -1};
//static enum bank_no cur_bank;
static int banksel_num = 0;
static int del_banksel_num = 0;
static int del_space_num = 0;
static hex_block *cf_head = NULL;
//hex_block *cf_curr = NULL;
static hex_block *cf_tail = NULL;

static MemBlock *om;			/*original MemBlock*/
static MemBlock *hm = NULL;		/*hex MemBlock*/
static FILE *dump;

/*-------------------------------------------------------------------------*/

/*--------------------------------------------------------------------------

---------------------------------------------------------------------------*/
static void dump_reloc_msg() {
	opt_msg *p = ptr_opt_head;
	int i = 0;
	fprintf(dump, "------------------dump_reloc_msg begin ------------\n");
	for (; p; p = p->next) {
		fprintf(dump, "(%x -- %x)\t", p->address>>1, p->value);
		if ((++i & 3) == 0)
			fprintf(dump, "\n");
	}
	fprintf(dump, "\n");
	fprintf(dump, "------------------dump_reloc_msg end --------------\n");
	fflush(dump);
	return;
}

/*---------------------------------------------------------------------------
	b_memory_put(m, byte_addr, word & 0xFF);
	b_memory_put(m, byte_addr + 1, word >> 8);
---------------------------------------------------------------------------*/
static void i_mask_le(MemBlock *m, unsigned int addr, unsigned short insn) {
	unsigned short value = 0;

	assert(m->memory);
	assert((addr >> I_MEM_BITS & 0xFFFF) == m->base);
	value = insn & 0xff;
	m->memory[addr & I_MEM_MASK] = value | BYTE_USED_MASK | BYTE_CAN_DELETE;
	/*write hign byte*/
	value = insn >> 8;
	m->memory[(addr + 1) & I_MEM_MASK] = value | BYTE_USED_MASK | BYTE_CAN_DELETE;
	
	return;
}

/*------------------------------------------------------------------------
clr psw, 5 -- ox6503
------------------------------------------------------------------------*/
static int is_bank0_insn(unsigned short i) {
	if (i == 0x6503)
		return 1;
	return 0;
}

/*------------------------------------------------------------------------
set psw, 5 -- ox6d03
------------------------------------------------------------------------*/
static int is_bank1_insn(unsigned short i) {
	if (i == 0x6d03)
		return 1;
	return 0;
}

/*------------------------------------------------------------------------------

-------------------------------------------------------------------------------*/
static int is_ret(unsigned short insn) {
	if ((insn >> 11 == 0x16) || insn == 0x8 || insn == 0x9)
		return 1;
	return 0;
}

/*-----------------------------------------------------------------------------

------------------------------------------------------------------------------*/
static int is_jmp(unsigned short insn) {
	if (insn >> 12 == 0xc)
		return 1;
	return 0;
}

/*------------------------------------------------------------------------------

-------------------------------------------------------------------------------*/
static int is_call(unsigned short insn) {
	if (insn >> 12 == 0xd)
		return 1;
	return 0;
}

/*-------------------------------------------------------------------------------

--------------------------------------------------------------------------------*/
static int is_absjmp(unsigned short insn) {
	if ((insn >> 12 == 0xc) || (insn >> 12 == 0xd))
		return 1;
	return 0;
}

/*------------------------------------------------------------------------
is it control tansfer instruction
	goto, call, return
if is, return 1, else 0.
-------------------------------------------------------------------------*/
static int is_transfer(unsigned short insn) {
	if (is_absjmp(insn) || is_ret(insn))
		return 1;
	return 0;
}

#if 0
/*---------------------------------------------------------------------------
typedef struct opt_msg_t {
	int value;
	struct opt_msg_t *next;
	unsigned short address;
	unsigned short is_flash_ref : 1;
} opt_msg;

extern opt_msg *ptr_opt_head;
extern opt_msg *ptr_opt_tail;
----------------------------------------------------------------------------*/
static void mk_main() {
	unsigned int addr = 0;
	unsigned short insn;
	int val;
	opt_msg *p;
	ptr_opt_tail->next = p = (opt_msg *)malloc(sizeof(opt_msg));
	assert(p);
	memset(p, 0, sizeof(opt_msg));
	ptr_opt_tail = p;
	assert(i_memory_get_le(om, addr, &insn));
	assert(is_jmp(insn));
	insn &= 0x0fff;
	insn = insn << 1 + 12;
	p->address = p->hex_addr = insn;
	/*set up value*/
	assert(i_memory_get_le(om, insn, &insn));
	assert(is_jmp(insn));
	insn &= 0x0fff;
	p->value = p->hex_val = insn;

	return;
}

#endif

/*----------------------------------------------------------------------------------

-----------------------------------------------------------------------------------*/
static void updata_msg(unsigned int d) {
	opt_msg *p = ptr_opt_head;
	unsigned short addr = (unsigned short)d;

	//unsigned short addr, value;
	for (; p; p = p->next) {
		if (addr < p->address) {
			assert(p->hex_addr >= 2);
			p->hex_addr -= 2;
		}
		if ((addr >> 1) < (unsigned short)p->value) {
			assert(p->hex_val >= 1);
			p->hex_val -= 1;
		}	
	}

	return;
}

/*-------------------------------------------------------------------------------

--------------------------------------------------------------------------------*/
static void updata_mb() {
	unsigned short insn, addr;
	unsigned short value;
	opt_msg *p = ptr_opt_head;
	//opt_msg *pp = ptr_opt_head;
	//make sure the last p'next item is NULL 
	for (; p; p = p->next) {
		addr = p->hex_addr;
		value = (unsigned short)p->hex_val;
		assert(i_memory_get_le(hm, addr, &insn));
		
		if (is_absjmp(insn))
			insn = (insn & 0xf000) | (value & 0xfff);
		else if (p->is_high)
			insn = (insn & 0xff00) | (value>>8 & 0xff);
		else
			insn = (insn & 0xff00) | (value & 0xff);

		i_memory_put_le(hm, addr, insn);
	}

	return;
}

/*----------------------------------------------------------------------------

----------------------------------------------------------------------------*/
static void new_block(unsigned int end) {
	/*cf_tail is point to the last one of hex_block list*/
	assert(cf_tail != NULL);
	cf_tail->end = end;
	cf_tail->next = (hex_block *)malloc(sizeof(hex_block));
	assert(cf_tail->next);
	memset(cf_tail->next, 0, sizeof(hex_block));
	cf_tail = cf_tail->next;
	//cf_tail->exit_blkno = bank_init;
	cf_tail->begin = end + 2;

	return;
}

/*----------------------------------------------------------------------------

-----------------------------------------------------------------------------*/
static void build_block() {
	unsigned short insn = 0;
	unsigned short value = 0;
	unsigned int addr = 0;		/*index the parameter m*/
	MemBlock *m = om;

	for (; addr < (4 * KF_CORE_SIZE); addr += 2) {		
		if (i_memory_get_le(m, addr, &insn) != 0) {
			if (is_transfer(insn)) 
				new_block(addr);
		/*if current word is unused in MeMBlock, must begin a new block*/
		} else {
			assert(addr > 1);
			assert(i_memory_get_le(m, addr - 2, &insn));
			if (is_transfer(insn) == 0)
				new_block(addr - 2);
			while (addr < (4 * KF_CORE_SIZE) && i_memory_get_le(m, addr += 2, &insn) == 0)
				;
			//update the current block begin index
			cf_tail->begin = addr;
			addr -= 2;
		}
	}
	/*the last block linked with (next pointer) is a empty block*/

	return;
}

/*------------------------------------------------------------------------------

-------------------------------------------------------------------------------*/
static void edge(hex_block *s, hex_block *d) {
	block_link **pp = &d->fore;
	//set up fore
	while (*pp) {
		if ((*pp)->ft == s)
			return;
		pp = &(*pp)->next;
	}
	*pp = (block_link *)malloc(sizeof(block_link));
	assert(*pp);
	(*pp)->next = NULL;
	(*pp)->ft = s;
	//set up succeed
	pp = &s->succ;
	while (*pp) {
		if ((*pp)->ft == d)
			return;
		pp = &(*pp)->next;
	}
	*pp = (block_link *)malloc(sizeof(block_link));
	assert(*pp);
	(*pp)->next = NULL;
	(*pp)->ft = d;
	
	return;
}

/*------------------------------------------------------------------------------

-------------------------------------------------------------------------------*/
static hex_block *find_block(unsigned int addr) {
	hex_block *p = cf_head;

	for (; p != cf_tail; p = p->next) {
		unsigned int begin = p->begin; 
		unsigned int end = p->end;
		if (addr >= begin && addr <= end)
			return p;
	}

	return NULL;
}

/*-----------------------------------------------------------------------------

-----------------------------------------------------------------------------*/
static void ch_link(hex_block *old, hex_block *now) {
	block_link *p, *q;

	for (p = old->succ; p; p = p->next)
		for (q = p->ft->fore; q; q = q->next)
			if (q->ft == old)
				q->ft = now;	

	return;
}

/*---------------------------------------------------------------------------
split one block to two from the point (parameter mid)
---------------------------------------------------------------------------*/
static hex_block *split(hex_block *curr, unsigned int mid) {
	hex_block *p = NULL;
	assert(mid > curr->begin && mid <= curr->end);
	p = (hex_block *)malloc(sizeof(hex_block));
	/*TODO: test malloc fail*/
	assert(p);
	memset(p, 0, sizeof(hex_block));
	ch_link(curr, p);
	p->succ = curr->succ;
	curr->succ = NULL;
	p->end = curr->end;
	curr->end = mid - 2;
	p->next = curr->next;
	curr->next = p;
	p->begin = mid;
	p->exit_blkno = bank_init;	/*this assignment for clear*/

	return p;
}

/*----------------------------------------------------------------------------
decrjz			09xx		
decjz			08xx
incrjz			0cxx		
decjz			0dxx
jnb dir, bit	0111_0bbb_ffff_ffff
jb dir, bit		0111_1bbb_ffff_ffff
-----------------------------------
jnb rd, bit		1111_0111_10bb_brrr
jb rd, bit		1111_0111_11bb_brrr
incjz rd		1111_1111_0101_0rrr
decjz rd		1111_1111_0101_1rrr
-----------------------------------------------------------------------------*/
static int is_testjmp(unsigned int addr) {
	unsigned short insn;
	int ret = i_memory_get_le(om, addr, &insn);
	if (ret && ((insn >> 8 == 0x8) || 
		(insn >> 8 == 0x9) || (insn >> 8 == 0xc) || (insn >> 8 == 0xd)
		|| (insn >> 11 == 0xe) || (insn >> 11 == 0xf)))
		return 1;
	
	return 0;
}

/*----------------------------------------------------------------------------

-----------------------------------------------------------------------------*/
static int no_test(unsigned int addr) {
	if (state.processor->maxrom < 0x400) {
		if (addr == 0x3ff || addr == 0x3fe || addr == 0x3fd || addr == 0x3fc)
			return 1;
	} else if (state.processor->maxrom < 0x800) {
		if (addr == 0x7ff || addr == 0x7fe || addr == 0x7fd || addr == 0x7fc)
			return 1;
	} else {
		if (addr == 0xfff || addr == 0xffe || addr == 0xffd || addr == 0xffc)
			return 1;
	}

	return 0;
}

/*----------------------------------------------------------------------------

-----------------------------------------------------------------------------*/
unsigned int find_value(unsigned int addr) {
	//unsigned int ret = 0;
	opt_msg *p = ptr_opt_head;
	for (; p; p = p->next)
		if (p->address == (unsigned short)addr)
			return p->value;
	assert(0);
}

/*----------------------------------------------------------------------------
build the control flow analysis graphic
----------------------------------------------------------------------------*/
static void build_cf() {
	hex_block *p = cf_head;
	unsigned int index;
	unsigned int addr;
	unsigned short insn;
	hex_block *fb = NULL;
	hex_block *tb = NULL;
	
	for (; p != cf_tail; p = p->next) {
		//control shift instruction must be the last one 
		index = p->end;
		assert(i_memory_get_le(om, index, &insn) != 0);
		addr = insn & 0x0fff;
		//addr = find_value(index);
		if (is_absjmp(insn) && !no_test(addr)) {
			addr = find_value(index);
			addr <<= 1;
			fb = find_block(addr);
			assert(fb);
			if (addr != fb->begin) {
				tb = split(fb, addr);
				/*control flow maybe from fb to tb*/
				edge(fb, tb);
			} else
				tb = fb;
			edge(p, tb);
			/*----------------------------------------------------------
			label:
				decjz something
				jmp	label
			----------------------------------------------------------*/
			/*if last instruction of prev block(linked with next pointer) 
				is call, trace the RET is difficult, so now not trace it*/
			if (is_call(insn) && p->next && p->next != cf_tail)
				p->next->entry_blkno = bank_undef;
			/*decjz; jmp/call;*/
			if (index > 1 && is_testjmp(index-2) && 
				p->next && p->next != cf_tail) {
				/*RETURN will go bank to the next instruction of call*/
				edge(p, p->next);				
			}
		/*didn't trace the execute flow, so i don't know RETURN will return where.
		to understand this need reference the statement dealing with CALL
		RETURN has no contribution to build the control flow*/
		} else if (is_ret(insn) && index > 1 && is_testjmp(index-2))
			if (p->next && p->next != cf_tail)
				edge(p, p->next);
	}//for

	return;
}

/*----------------------------------------------------------------------------

-----------------------------------------------------------------------------*/
static void init_block() {
	cf_head = cf_tail = (hex_block *)malloc(sizeof(hex_block));
	memset(cf_head, 0, sizeof(hex_block));
	cf_tail->begin = 0;		/*write this clear, through it is useless*/
	//cf_tail->exit_blkno = bank_init;
	//cf_tail->next = NULL;

	return;
}

#if 0
/*---------------------------------------------------------------------------

----------------------------------------------------------------------------*/
void make_di(unsigned int addr) {
	del_idx **p = &di_head;

	if (di_head == NULL)
		di_head = (del_idx *)malloc(sizeof(del_idx));
	for (; *p ;*p = (*p)->next) 
		;
	*p = (del_idx *)malloc(sizeof(del_idx));
	(*p)->index = addr;
	/*will use this NULL to test the last*/
	(*p)->next = NULL;	

	return;
}

/*----------------------------------------------------------------------------
mask the banksel direct which one can be delete, the first banksel of a block
	must be keep, the next pass will deal with this first banksel.
----------------------------------------------------------------------------*/
static void mask_db_discard(MemBlock *m) {
	hex_block *p = cf_head;
	unsigned short insn;
	unsigned int addr;
	enum bank_no curr_bank = bank_init;

	for (; p != cf_tail; p = p->next) {
		assert(p->begin <= p->end);
		for (addr = p->begin; addr <= p->end; addr += 2) {
			assert(i_memory_get_le(m, addr, &insn));
			if (is_bank0_insn(insn))
				if (curr_bank == bank_0)
					i_mask_le(m, addr, insn);
				else
					curr_bank = bank_0;
			else if (is_bank1_insn(insn))
				if (curr_bank == bank_1)
					i_mask_le(m, addr, insn);
				else
					curr_bank = bank_1;
		}
		/*important point*/
		p->exit_blkno = curr_bank;	
	}

	return;
}

/*--------------------------------------------------------------------------
generate more accurate message about which first banksel of a block can be 
	deleted
---------------------------------------------------------------------------*/
static void accu_db(MemBlock *m) {
	hex_block *ph = cf_head;
	//del_idx **ppd = &di_head;
	enum bank_no n;
	block_link *pb = NULL;
	/*TODO: need complex graphic travel,
		ph->exit_blkno == bank_init;--> means this block has not banksel
		ph->entry_blkno == bank_undef;--> means the last instruction of prev block is CALL*/
	for (; ph != cf_tail && ph->exit_blkno != bank_init && 
			ph->entry_blkno == bank_undef; ph = ph->next)
		if ((n = has_ib(ph->fore)) != bank_init && n != bank_undef)
			test_fb(ph, n);
			
	return;
}

/*---------------------------------------------------------------------------
test the first banksel, if it is identical with parameter bn, delete it
---------------------------------------------------------------------------*/
static void test_fb(hex_block *p, enum bank_no bn) {
	unsigned int idx = p->begin;
	unsigned short insn;
	MemBlock *m = om;

	for (; idx <= p->end; idx += 2) {
		assert(i_memory_get_le(m, idx, &insn));
		if (is_bank0_insn(insn) && bn == bank_0) {
			i_mask_le(m, idx, insn);
			break;
		}
		else if (is_bank1_insn(insn) && bn == bank_1) {
			i_mask_le(m, idx, insn);
			break;
		}
	}

	return;
}

#endif

/*--------------------------------------------------------------------------
is it identical bank ? if so return the bank number, else return bank_undef
---------------------------------------------------------------------------*/
enum bank_no has_ib(block_link *p) {
	block_link *pb = p;
	enum bank_no n = bank_undef;
	hex_block *t = NULL;

	if (pb == NULL)
		return bank_undef;
	n = pb->ft->exit_blkno;
	for (pb = pb->next; pb; pb = pb->next) {
		assert(t = pb->ft);			/*intend to assignment, not mistake*/
		if (n != t->exit_blkno)
			return bank_undef;
	}

	return n;
}

/*----------------------------------------------------------------------------

----------------------------------------------------------------------------*/
static void entry_blk(hex_block *p) {
	/*entry_blkno : 
	bank_undef -- the block's fore blocks have not identical bank
	bank_init -- all the fore blocks of this block have not banksel
	bank_0 -- the block's fore blocks have identical bank bank 0
	bank_1 -- the block's fore blocks have identical bank bank 1*/		
	if (p->entry_blkno == bank_init && p->fore)
		p->entry_blkno = has_ib(p->fore);
	
	return;
}

/*----------------------------------------------------------------------------
mask the banksel can be deleted, and propagate the bank_no from entry to exit 
-----------------------------------------------------------------------------*/
static void mask_db(hex_block *p) {
	unsigned short insn;
	unsigned int addr;
	enum bank_no curr_bank;

	assert(p->begin <= p->end);
	/*make sure the entry_blkno of every block*/
	entry_blk(p);
	curr_bank = p->entry_blkno;
	/*mask all the banksel can be deleted
	Attentions, code like this :
		decjz something
		banksel id
	NOTE :the "banksel id" can not be deleted at every time and condtion.*/
	for (addr = p->begin; addr <= p->end; addr += 2) {
		assert(i_memory_get_le(om, addr, &insn));
#if 0
		if (is_bank0_insn(insn))
			if (curr_bank == bank_0)
				i_mask_le(om, addr, insn);
			else
				curr_bank = bank_0;
		else if (is_bank1_insn(insn))
			if (curr_bank == bank_1)
				i_mask_le(om, addr, insn);
			else
				curr_bank = bank_1;
#endif

		if (is_bank0_insn(insn)) {
			banksel_num++;
			if (curr_bank == bank_0) {
				if (addr-2 >= p->begin && !is_testjmp(addr-2) || addr-2 < p->begin)
					i_mask_le(om, addr, insn);
			} else
				if (addr-2 >= p->begin && is_testjmp(addr-2))
					curr_bank = bank_undef;
				else
					curr_bank = bank_0;
		} else if (is_bank1_insn(insn)) {
			banksel_num++;
			if (curr_bank == bank_1) {
				if (addr-2 >= p->begin && !is_testjmp(addr-2) || addr-2 < p->begin)
					i_mask_le(om, addr, insn);
			} else
				if (addr-2 >= p->begin && is_testjmp(addr-2))
					curr_bank = bank_undef;
				else
					curr_bank = bank_1;
		}

	}
	/*important point*/
	p->exit_blkno = curr_bank;

	return;
}

/*----------------------------------------------------------------------------
exit_blkno is appoint by the last banksel of this block, 
	otherwise is bank_undef, this is cautious.
	the bank_undef will cause the succeed block always keep its first banksel
-----------------------------------------------------------------------------*/
static void exit_blk(hex_block *p) {
	unsigned short insn;
	unsigned int addr;
	enum bank_no curr_bank = bank_undef;
	/*if the exit_blkno id not bank_init, 
		we have called this function with some argument*/
	if (p->exit_blkno != bank_init)
		return;
	for (addr = p->end; addr >= p->begin && addr <= p->end; addr -= 2) {
		assert(i_memory_get_le(om, addr, &insn));
		if (is_bank0_insn(insn))
			curr_bank = bank_0;
		else if (is_bank1_insn(insn))
			curr_bank = bank_1;
	}
	p->exit_blkno = curr_bank;

	return;
}

/*----------------------------------------------------------------------------

-----------------------------------------------------------------------------*/
static void mask_db_dfs(hex_block *ph) {
	block_link *pb;
	//hex_block *p = ph;
	if (ph->visited)
		return;
	ph->visting = 1;	

	/*this block rely on the exit_blkno of its fore block*/
	for (pb = ph->fore; pb; pb = pb->next) {
		/*if this block can jump to itself, first decide it's exit_blkno*/
		if (pb->ft->visting) {
			exit_blk(pb->ft);
			continue;
		}
		mask_db_dfs(pb->ft);
	}
	mask_db(ph);
	/*after all the BANKSEL which can be deleted has be marked, block's visited set*/
	ph->visited = 1;
	ph->visting = 0;

	return;
}

/*---------------------------------------------------------------------------

----------------------------------------------------------------------------*/
static void wrap_mask_db_dfs() {
	hex_block *ph;

	for (ph = cf_head; ph != cf_tail; ph = ph->next)
		mask_db_dfs(ph);

	return;
}

/*--------------------------------------------------------------------------
if return 1 : just like the b_memery_get() return 1;
if return 2 : the word in the MemBlock is a BANKSEL can be deleted;
---------------------------------------------------------------------------*/
static int b_mask_get(MemBlock *m, unsigned int address, 
		unsigned char *byte) {
	unsigned short us = 0;

	assert(m->memory != NULL);
	if (((address >> I_MEM_BITS) & 0xFFFF) == m->base) {
		us = m->memory[address & I_MEM_MASK];
		*byte = us & 0xFF;

		if (us & BYTE_USED_MASK)
			if (us & BYTE_CAN_DELETE)
				return 2;
			else
				return 1;
	}

	return 0;
}

/*--------------------------------------------------------------------------

---------------------------------------------------------------------------*/
static int i_mask_get_le(MemBlock *m, unsigned int byte_addr, 
		unsigned short *word) {
	unsigned char bytes[2];
	int ret1 = b_mask_get(m, byte_addr, bytes);
	int ret2 = b_mask_get(m, byte_addr + 1, bytes + 1);

	if (ret1 && ret2) {
		*word = bytes[0] + (bytes[1] << 8);
		assert(ret1 == ret2);
		return ret1;
	}

	return 0;
}

/*--------------------------------------------------------------------------

---------------------------------------------------------------------------*/
static void dump_block(int pass) {
	hex_block *p = cf_head;
	int i = 0;

	if (pass == 1)
		fprintf(dump, "******dump_block before control flow analysis******\n");
	else if (pass == 2)
		fprintf(dump, "------dump_block after control flow analysis-------\n");
	fprintf(dump, "(block begin -- block end)\n");
	fprintf(dump, "------------    ----------\n");
	for (; p; p = p->next) {
		fprintf(dump, "(%5x -- %5x)\t\t", p->begin >> 1, p->end >> 1);
		if ((++i & 3) == 0)
			fprintf(dump, "\n");
	}
	fprintf(dump, "\n");
	if (pass == 1) 
		fprintf(dump, "****dump_block end before control flow analysis****\n");
	else if (pass == 2)
		fprintf(dump, "----dump_block end after control flow analysis-----\n");
	fflush(dump);

	return;
}

/*----------------------------------------------------------------------------

----------------------------------------------------------------------------*/
static void dump_cf(int pass) {
	hex_block *p = cf_head;

	if (pass == 1)
		fprintf(dump, "-----------dump control flow analysis begin------------\n");
	else if (pass == 2)
		fprintf(dump, "-----------dump mask deleted banksel begin------------\n");
	fprintf(dump, "(block's last address, entry_blkno, exit_blkno)\n");
	fprintf(dump, "---------------------  -----------  -----------\n");
	for (; p; p = p->next) {
		block_link *pb = p->fore;
		fprintf(dump, "jump from :");
		if (pb == NULL)
			fprintf(dump, "NULL\t");
		for (; pb; pb = pb->next)
			fprintf(dump, "(%4x-%4x, %d, %d)", pb->ft->begin >> 1, pb->ft->end >> 1, 
				pb->ft->entry_blkno, pb->ft->exit_blkno);
		fprintf(dump, "\t -->\t(%4x-%4x, %d, %d)\n", p->begin >> 1, p->end >> 1,
				p->entry_blkno, p->exit_blkno);
	}
	if (pass == 1)
		fprintf(dump, "------------dump control flow analysis end-------------\n");
	else if (pass == 2)
		fprintf(dump, "------------dump mask deleted banksel end-------------\n");
	fflush(dump);

	return;
}

/*----------------------------------------------------------------------------

-----------------------------------------------------------------------------*/
static void write_ee(ee_data *ee, unsigned int occupy) {
	int curr_addr = state.processor->maxrom + 1;
	int count = 0;
	ee_data *p;
	
	if (!ee)
		return;
	//if (state.processor->maxrom + 10 > state.processor->badrom[0]) {
	//	printf("%s has no EEPROM\n", state.processor->names[0]);
	//	return;
	//}
	if (occupy>>1 > curr_addr) {
		printf("EEPROM at %x has been occupied\n", curr_addr);
		return;
	}
	for (p = ee; p; p = p->next) {
		int i;
		if (p->a)
			curr_addr = p->a;
		for (i = 0; i < 8; i++) {
			unsigned short insn;
			insn = p->d[i];
			i_memory_put_le(hm, (curr_addr+i)<<1, insn);
		}
		
		curr_addr += 8;
	}
	if (curr_addr > state.processor->badrom[0])
		printf("EEPROM overflow\n");

	return;
}

/*--------------------------------------------------------------------------
the main function of banksel optimzation

typedef struct opt_msg_t {
	int value;
	struct opt_msg_t *next;
	unsigned short address;
	unsigned short is_flash_ref : 1;
} opt_msg;

extern opt_msg *ptr_opt_head;
extern opt_msg *ptr_opt_tail;
extern int opt_errors;
---------------------------------------------------------------------------*/
MemBlock *bank_opt(MemBlock *m, unsigned int core_size) {
	unsigned short insn = 0;
	unsigned short value = 0;
	unsigned int addr = 0;		/*index the parameter m*/
	unsigned int hm_idx = 0;
	int ret = 0;
	om = m;
	//assert(om);
	//cur_bank = bank_init;
	hm = i_memory_create();
	//mk_main();
	dump = fopen("dump_bank_opt", "wt");
	//assert(dump);
	dump_reloc_msg();
	/*block control flow analysis*/
	init_block();
	build_block();
	/*TODO*/
	//dump_block(1);
	build_cf();
	dump_block(2);
	//dump_cf(1);
	wrap_mask_db_dfs();
	dump_cf(2);
	/*the second pass deal with the first BANKSEL of one block
		this pass this aggressive*/
	/*TODO, this function need be called many times until all block has no change*/
	//accu_db(m);
	/*copy the 0 ~ 4, because of the special address 0004*/
	while (addr < 8) {
		if (i_memory_get_le(m, addr, &insn))
			i_memory_put_le(hm, addr, insn);
		addr += 2;
	} 
	
	assert(addr == 8);
	for(hm_idx = addr; addr < (4 * KF_CORE_SIZE); addr += 2) {
		ret = i_mask_get_le(om, addr, &insn);
		if (ret == 1) {
			i_memory_put_le(hm, hm_idx, insn);
			if (!state.no_excess_error && (hm_idx >> 1) > state.processor->maxrom) {
				gp_error("no target memory available after BANKSEL optimization\n");
				goto ret;
			}
			hm_idx += 2;			
		} else if (ret == 2) {
			updata_msg(addr);
			del_banksel_num ++;
		} else {
			assert(ret == 0);
			if (addr < cf_tail->begin) {
				updata_msg(addr);
				del_space_num++;
			}
		}
#if 0
		if (i_memory_get_le(m, addr, &insn)) {
			if (is_transfer(insn)) {
				cur_bank = bank_undef;
				i_memory_put_le(hm, hm_idx, insn);
				hm_idx += 2;
			} else if (is_bank0_insn(insn)) {
				if (cur_bank == bank_0) {
					updata_msg(addr);
					del_banksel_num ++;
				} else {
					cur_bank = bank_0;
					i_memory_put_le(hm, hm_idx, insn);
					hm_idx += 2;
				}
			} else if (is_bank1_insn(insn)) {
				if (cur_bank == bank_1) {
					updata_msg(addr);
					del_banksel_num ++;
				} else {
					cur_bank = bank_1;
					i_memory_put_le(hm, hm_idx, insn);
					hm_idx += 2;
				}
			} else {
				i_memory_put_le(hm, hm_idx, insn);
				hm_idx += 2;
			}		
		} else
			updata_msg(addr);
			//addr += 2;
#endif
	}

	for(addr = (4 * KF_CORE_SIZE); addr < core_size; addr += 2) {
		if (i_memory_get_le(om, addr, &insn))
			i_memory_put_le(hm, addr, insn);
	}

	/*the most important step*/
	updata_mb();
	/*write eeprom data*/
	//if (state.ee.ee_enabled)
		write_ee(parse_ee(), hm_idx);
	if (opt_errors) {
		printf("the BANKSEL optimization will not execute\n");
		return m;
	}
	
	printf("all the BANKSEL number is %d\n", banksel_num);
	printf("deleted BANKSEL number is %d\n", del_banksel_num);
	printf("the last instruction address is %x\n", (hm_idx>>1));
	//printf("delete space number is %d\n", del_space_num);
ret:
	return hm;
}
