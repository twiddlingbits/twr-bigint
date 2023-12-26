#include "twr-bigint.h"
#include <assert.h>

static int get_used_word_count(struct twr_bigint * bi) {
	int i=BIG_INT_WORD_COUNT-1;
	while (i>0 && bi->word[i]==0) i--;
	return i+1;
}

void twr_big_bzero(struct twr_bigint * big) {
	for (int i=0; i<BIG_INT_WORD_COUNT; i++)
		big->word[i]=0;
}

void twr_big_bmax(struct twr_bigint * big) {
	for (int i=0; i<BIG_INT_WORD_COUNT; i++)
		big->word[i]=UINT32_MAX;
}

int twr_big_iszero(struct twr_bigint * big) {
	for (int i=0; i<BIG_INT_WORD_COUNT; i++)
		if (big->word[i]) return 0;

	return 1;
}

int twr_big_isequal(struct twr_bigint * big1, struct twr_bigint * big2) {
	for (int i=0; i<BIG_INT_WORD_COUNT; i++)
		if (big1->word[i]!=big2->word[i]) return 0;

	return 1;
}

/* big1 >= big2 */
int twr_big_isgteq(struct twr_bigint * big1, struct twr_bigint * big2) {

	for (int i=BIG_INT_WORD_COUNT-1; i>=0; i--) {
		if (big1->word[i]==big2->word[i]) continue;
		if (big1->word[i]>big2->word[i]) return 1; else return 0;
	}

	return 1;
}

int twr_big_isgt(struct twr_bigint * big1, struct twr_bigint * big2) {

	for (int i=BIG_INT_WORD_COUNT-1; i>=0; i--) {
		if (big1->word[i]==big2->word[i]) continue;
		if (big1->word[i] > big2->word[i]) return 1; else return 0;
	}

	return 0;
}

/* big1 <= big2 */
int twr_big_islteq(struct twr_bigint * big1, struct twr_bigint * big2) {
	return twr_big_isgteq(big2, big1);
}

int twr_big_islt(struct twr_bigint * big1, struct twr_bigint * big2) {
	return twr_big_isgt(big2, big1);
}

int twr_big_2pow(struct twr_bigint * big, unsigned int exp) {
	if (exp >=  BIG_INT_WORD_COUNT*32) return 1;
	twr_big_bzero(big);
	big->word[exp/32]=1<<(exp%32);

	return 0;
}

void twr_big_assign32u(struct twr_bigint * big, uint32_t ui) {
	twr_big_bzero(big);
	big->word[0]=ui;
}

void twr_big_assign64u(struct twr_bigint * big, uint64_t ui) {
	twr_big_bzero(big);
	big->word[0]=ui&0xFFFFFFFF;
	big->word[1]=ui>>32;
}

void twr_big_assign128u(struct twr_bigint * big, uint64_t u1, uint64_t u2) {
	twr_big_bzero(big);
	big->word[0]=u2&0xFFFFFFFF;
	big->word[1]=u2>>32;
	big->word[2]=u1&0xFFFFFFFF;
	big->word[3]=u1>>32;
}

void twr_big_assign(struct twr_bigint *dest, struct twr_bigint * source) {
	for (int i=0; i<BIG_INT_WORD_COUNT; i++)
		dest->word[i]=source->word[i];
}

int twr_big_mult32u(struct twr_bigint * product, struct twr_bigint * multiplicand, uint32_t multipler) {

	uint32_t carry=0;

	for (int i=0; i<BIG_INT_WORD_COUNT; i++) {
		uint64_t partialprodcut=(uint64_t)multipler*multiplicand->word[i];
		partialprodcut+=carry;
		product->word[i]=partialprodcut&0xFFFFFFFF;
		carry=partialprodcut>>32;
	}	

	return carry;
}

/*returns 0 if no error, 1 if overflow */

int twr_big_10pow(struct twr_bigint * big, unsigned int base, unsigned int exp) {
	twr_big_assign32u(big, 1);
	while (exp--)
		if (twr_big_mult32u(big, big, base)) return 1;

	return 0;
}

/** 0 if no error; 1 if bit(s) lost  (non-zero words shift out end) */
int twr_big_shiftleft_words(struct twr_bigint * bi, unsigned int n) {

	if (n==0) return 0;

	int lostbits = (n>=BIG_INT_WORD_COUNT);
	if (lostbits) {
		twr_big_bzero(bi);
		return lostbits;
	}

	int move=BIG_INT_WORD_COUNT-n;
	assert (move >= 1 && move < BIG_INT_WORD_COUNT);

	int dest=BIG_INT_WORD_COUNT-1;
	int src=dest-n;

/** these are words that didn't get touched below beacuse they would be moved outside the word */
/** a non zero word here means bits were lost in the shift */
	for (int i=src+1; i<dest; i++) {
		if (bi->word[i]!=0) lostbits=1;
		bi->word[i]=0;
	}

	for (unsigned int i=0; i < n; i++)
	if (bi->word[BIG_INT_WORD_COUNT-1-i]!=0) lostbits=1;

	while (move--) {
		bi->word[dest--]=bi->word[src];
		bi->word[src--]=0;
	}

	assert(src==-1);

	return lostbits;
}

/** 0 if no error; 1 if bit(s) lost  (non-zero words shift out end) */
int twr_big_shiftright_words(struct twr_bigint * bi, unsigned int n) {

	if (n==0) return 0;

	int lostbits = (n>=BIG_INT_WORD_COUNT);
	if (lostbits) {
		twr_big_bzero(bi);
		return lostbits;
	}

	int move=BIG_INT_WORD_COUNT-n;
	assert (move >= 1 && move < BIG_INT_WORD_COUNT);

	int dest=0;
	int src=n;
	/** these are words that didn't get touched below beacuse they would be moved outside the word */
	/** a non zero word here means bits were lost in the shift */
	for (int i=dest+move; i<=(src-1); i++) {
		if (bi->word[i]!=0) lostbits=1;
		bi->word[i]=0;
	}

for (unsigned int i=0; i < n; i++)
	if (bi->word[i]!=0) lostbits=1;

/* move words */
	while (move--) {
		bi->word[dest++]=bi->word[src];
		bi->word[src++]=0;
	}

	assert(src==BIG_INT_WORD_COUNT);

	return lostbits;
}


int twr_big_shiftleft_onebit(struct twr_bigint * bi) {
	int carry=0;

	for (int i=0; i<BIG_INT_WORD_COUNT; i++) {
		int t=bi->word[i]&(1<<31);
		bi->word[i]<<=1;
		if (carry) bi->word[i]|=1;
		carry=t;
	}
	return carry;
}

/* returns 1 if bit lost */
int twr_big_shiftright_onebit(struct twr_bigint * bi) {
	int carry;
	int bitzero=bi->word[0]&1;
	for (int i=0; i<BIG_INT_WORD_COUNT-1; i++) {
		carry=bi->word[i+1]&1;
		bi->word[i]>>=1;
		if (carry) bi->word[i]|=(1<<31);
	}
	bi->word[BIG_INT_WORD_COUNT-1]>>=1;

	return bitzero;
}

int twr_big_shiftleft_bits(struct twr_bigint * bi, unsigned int n) {
	int lostbits;
	lostbits=twr_big_shiftleft_words(bi, n/32);
	for (unsigned int i=0; i < (n%32); i++)
		lostbits=lostbits|twr_big_shiftleft_onebit(bi);

	return lostbits;
}

int twr_big_shiftright_bits(struct twr_bigint * bi, unsigned int n) {
	int lostbits;
	lostbits=twr_big_shiftright_words(bi, n/32);
	for (unsigned int i=0; i < (n%32); i++)
		lostbits=lostbits|twr_big_shiftright_onebit(bi);

	return lostbits;
}

void twr_big_set_bit(struct twr_bigint * big, unsigned int bitnum, unsigned int val) {
	if (val)
		big->word[bitnum/32]|=(1<<(bitnum%32));
	else
		big->word[bitnum/32]&=(~(1<<(bitnum%32)));
}

int twr_big_get_bit(struct twr_bigint * big, unsigned int bitnum) {
	if (big->word[bitnum/32]&(1<<(bitnum%32)))
		return 1;
	else
		return 0;
}

int twr_big_add(struct twr_bigint * sum, struct twr_bigint * addend1, struct twr_bigint * addend2) {
	uint32_t carry=0, tc, s;

	for (int i=0; i<BIG_INT_WORD_COUNT; i++) {
		const uint32_t a=addend1->word[i];
		const uint32_t b=addend2->word[i];

		s=a+b;
		if ( s < a ) tc=1; else tc=0;  /* overflow? */

		s=s+carry;
		if (s<carry || tc==1) carry=1; else carry=0;   /* overflow? */

		sum->word[i]=s;
	}

	return carry;
}


int twr_big_add32u(struct twr_bigint * sum, struct twr_bigint *addend1 , uint32_t b) {
	uint32_t carry, s;

	const uint32_t a=addend1->word[0];
	s=a+b;
	if ( s < a ) carry=1; else carry=0;  	/* overflow? */
	sum->word[0]=s;

	for (int i=1; i<BIG_INT_WORD_COUNT; i++) {
		const uint32_t a=addend1->word[i];
		s=a+carry;
		if (s<carry) carry=1; else carry=0;   /* overflow? */
		sum->word[i]=s;
	}

	return carry;
}

void twr_big_complement(struct twr_bigint * result, struct twr_bigint * in) {
	for (int i=0; i<BIG_INT_WORD_COUNT; i++) 
		result->word[i]=~(in->word[i]);
}

/* r = a - b */
void twr_big_sub(struct twr_bigint * r, struct twr_bigint * a, struct twr_bigint * b) {
	struct twr_bigint twos;
	twr_big_complement(&twos, b);
	twr_big_add32u(&twos, &twos, 1);
	
	twr_big_add(r, a, &twos);

/**

	uint64_t borrow=0;
	uint64_t newborrowa, newborrowb;

	for (int i=0; i<BIG_INT_WORD_COUNT; i++) {
		if ((uint64_t)a->word[i] >= (uint64_t)b->word[i] + borrow) {
			newborrowa=0;
			newborrowb=0;

		}
		else {
			newborrowa=1+UINT32_MAX;
			newborrowb=1;
		}
			
		r->word[i]=(uint64_t)(a->word[i]) + newborrowa - borrow - (uint64_t)(b->word[i]);

		borrow=newborrowb;
	}	

	return borrow;

**/

}

/* returns error num; 0 no error.  1 overflow. */

int twr_big_mult(struct twr_bigint * product, struct twr_bigint * multiplicand, struct twr_bigint * multipler) {
	struct twr_bigint t;
	struct twr_bigint tps;
	struct twr_bigint *tp;

	if (product==multiplicand || product==multipler)
		tp=&tps;
	else
		tp=product;

	twr_big_bzero(tp);

	const int wc=get_used_word_count(multipler);

	for (int i=0; i<wc; i++) {
		if (twr_big_mult32u(&t, multiplicand, multipler->word[i])) return 1;
		if (twr_big_shiftleft_words(&t, i)) return 1;
		if (twr_big_add(tp, tp, &t)) return 1;
	}

	if (tp==&tps)
		twr_big_assign(product, tp);

	return 0;
}

void twr_big_div(struct twr_bigint * q, struct twr_bigint * r, struct twr_bigint * num, struct twr_bigint * den) {
	struct twr_bigint qt;
	struct twr_bigint rt;

	if (r==NULL) r=&rt;

	twr_big_bzero(r);

	if (twr_big_iszero(den)) {
		twr_big_bmax(q);
		return;
	}

	twr_big_bzero(&qt);
	/*
	for i := n − 1 .. 0 do  -- Where n is number of bits in N
	R := R << 1           -- Left-shift R by 1 bit
	R(0) := N(i)          -- Set the least-significant bit of R equal to bit i of the numerator
	if R ≥ D then
		R := R − D
		Q(i) := 1
	end
	end
	*/

	for (int i=get_used_word_count(num)*32-1; i>=0; i--) {
		twr_big_shiftleft_onebit(r);
		twr_big_set_bit(r, 0, twr_big_get_bit(num, i));
		if (twr_big_isgteq(r, den)) {
			twr_big_sub(r, r, den);
			twr_big_set_bit(&qt, i, 1);
		}
	}
	twr_big_assign(q, &qt);
}

uint32_t twr_big_get32u(struct twr_bigint * big) {
		return big->word[0];
}

int twr_big_isint32u(struct twr_bigint * big) {
	for (int i=1; i < BIG_INT_WORD_COUNT; i++)
		if (big->word[i]>0) return 0;

	return 1;
}

int twr_big_10log(struct twr_bigint * numin, struct twr_bigint * denin) {
	int logval=0;

	if (twr_big_iszero(numin)) return -1;

	if (twr_big_isgteq(numin, denin)) { /** >=1 */
		struct twr_bigint den, den10;
		twr_big_assign(&den, denin);

		while (1) {
			/*
			twr_big_div(&q, &r, numin, &den); 
			if (twr_big_isint32u(&q) && (twr_big_get32u(&q)>=1 && twr_big_get32u(&q)<=9)) return logval;
			*/
			if (twr_big_mult32u(&den10, &den, 10)) return logval;
			if (twr_big_isgteq(numin, &den) && twr_big_islt(numin, &den10)) return logval;

			logval++;
			twr_big_assign(&den, &den10);  // divide by 10
		}
	}
	else {
		struct twr_bigint num, num10;
		twr_big_assign(&num, numin);

		while (1) {
			/*
			twr_big_div(&q, &r, &num, denin); 
			if (twr_big_isint32u(&q) && (twr_big_get32u(&q)>=1 && twr_big_get32u(&q)<=9)) {
				return -logval;
			} 
			*/

			logval++;  /* both log 0.1 and log 0.9 return -1 */
			if(twr_big_mult32u(&num10, &num, 10)) return -logval;
			if (twr_big_isgt(denin, &num) && twr_big_islteq(denin, &num10)) return -logval;
			twr_big_assign(&num, &num10);
		}
	}
}

int twr_big_2log(struct twr_bigint * numin, struct twr_bigint * denin) {
	int logval=0;

	if (twr_big_iszero(numin)) return BIGINT_LOG_OFZERO_ERROR;

	if (twr_big_isequal(numin, denin)) return 0;

	if (twr_big_isgt(numin, denin)) { /** >1 */
		struct twr_bigint den, den2;
		twr_big_assign(&den, denin);

		while (1) {
			twr_big_assign(&den2, &den);
			int carry=twr_big_shiftleft_onebit(&den2); // *2
			if (carry!=0) return logval;
			if (twr_big_isgteq(numin, &den) && twr_big_islt(numin, &den2)) return logval;			
			logval++;
			twr_big_assign(&den, &den2);
		}
	}
	else {
		struct twr_bigint num, num2;
		twr_big_assign(&num, numin);

		while (1) {
			twr_big_assign(&num2, &num);
			int carry=twr_big_shiftleft_onebit(&num2); // *2
			logval++;  /* both log 0.1 and log 0.9 return -1 */
			if (carry!=0) 
				return -logval;
			if (twr_big_isgt(denin, &num) && twr_big_islteq(denin, &num2)) return -logval;
			twr_big_assign(&num, &num2);
		}
	}
}

uint32_t twr_big_num10digits(struct twr_bigint * numberin) {
	int count = 0; 
	struct twr_bigint ten, number;

	twr_big_assign32u(&ten, 10);
	twr_big_assign(&number, numberin);

	do { 
		twr_big_div(&number, 0, &number, &ten);
		//number = number / 10; 
		++count; 
	} while (!twr_big_iszero(&number));

	return count;
}

static void _strhorizflip(char * buffer, int n) {
	for (int k=0; k<n/2;k++)  {
		char t=buffer[k];
		buffer[k]=buffer[n-k-1];
		buffer[n-k-1]=t;
	}
}

int twr_big_itoa(struct twr_bigint * valuein, char * buffer, int size, int radixin) {
	int i=0;
	const char *digitchars="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
	struct twr_bigint value, rem, radix, den;

	if (size < 1) return 1;  /* error - buffer too small */

	if (radixin < 2 || radixin > 36)
		return 2;  /* invalid radix */

	twr_big_assign(&value, valuein);
	twr_big_assign32u(&den, 1);
	twr_big_assign32u(&radix, radixin);

/** big currently doesnt support negative numbers */
//	if (value<0) {
//		value=-value;
//		if (size < 3) return 1;  /* error - buffer too small */
//		buffer[i++]='-';
//	}

	const int istart=i;

	while (1) {
		if (i>=(size-1)) return 1; /* error - buffer too small */
		twr_big_div(&value, &rem, valuein, &den);  		// vaue=value/radix
		twr_big_div(&value, &rem, &value, &radix);  		// digit=value%radix;
		int overflow=twr_big_mult32u(&den, &den, radixin);
		assert(!overflow);
		buffer[i++]=digitchars[rem.word[0]];
		if (twr_big_iszero(&value)) {
			_strhorizflip(buffer+istart, i-istart);
			buffer[i]=0;
			return 0;
		}
	}
}

static int _isdigit(int c) {
	return c>='0' && c<='9';
}

int twr_big_atoi(const char *str, struct twr_bigint *result) {
	twr_big_bzero(result);
	int num_digits=0;

	while (_isdigit(str[num_digits])) {
		int overflow=twr_big_mult32u(result, result, 10);
		assert(!overflow);
		overflow=twr_big_add32u(result, result, str[num_digits]-'0');
		assert(!overflow);
		num_digits++;
	}

	return num_digits;
}

int twr_big_run_unit_tests() {
	struct twr_bigint a;
	struct twr_bigint b;
	struct twr_bigint c;

	twr_big_bzero(&a);
	if (!twr_big_iszero(&a)) return 0;

	twr_big_assign64u(&a, 1ULL<<32 | 1);
	if (!twr_big_shiftleft_words(&a, 63)) return 0;

	twr_big_2pow(&a, BIG_INT_WORD_COUNT*32-1);  // set high bit
	if (!twr_big_shiftleft_words(&a, 1)) return 0;
	if (!twr_big_iszero(&a)) return 0;

	twr_big_2pow(&a, BIG_INT_WORD_COUNT*32-1);  // set high bit
	if (!twr_big_shiftleft_onebit(&a)) return 0;
	if (!twr_big_iszero(&a)) return 0;

	twr_big_assign32u(&a,  1<<31);
	if (twr_big_shiftleft_words(&a, 63)) return 0;
	twr_big_2pow(&b, 31+63*32);
	if (!twr_big_isequal(&a, &b)) return 0;

	twr_big_2pow(&a, BIG_INT_WORD_COUNT*32-1);  // set high bit
	if (twr_big_shiftright_words(&a, 63)) return 0;

	twr_big_assign32u(&a,  1<<31);
	if (!twr_big_shiftright_words(&a, 1)) return 0;

	twr_big_assign32u(&b, 1);
	twr_big_bmax(&a);
	for (int i=0; i < 64*32-1; i++)
		if (!twr_big_shiftright_onebit(&a)) 
			return 0;
	if (!twr_big_isequal(&a, &b)) return 0;

	twr_big_bmax(&a);
	if (!twr_big_shiftright_bits(&a, BIG_INT_WORD_COUNT*32-1)) return 0;
	if (!twr_big_isequal(&a, &b)) return 0;
	
	twr_big_bmax(&a);
	twr_big_add32u(&a, &a, 1);
	if (!twr_big_iszero(&a)) return 0;
	if (!twr_big_isint32u(&a)) return 0;

	twr_big_assign32u(&a, UINT32_MAX);
	twr_big_add32u(&a, &a, 1);
	if (twr_big_iszero(&a)) return 0;
	if (twr_big_isint32u(&a)) return 0;

	twr_big_2pow(&a, 52);
	twr_big_2pow(&b, 52);
	if (!twr_big_isequal(&a, &b)) return 0;
	if (!twr_big_isgteq(&a, &b)) return 0;
	if (!twr_big_islteq(&a, &b)) return 0;
	if (twr_big_islt(&a, &b)) return 0;
	if (twr_big_isgt(&a, &b)) return 0;
	
	twr_big_2pow(&b, 100);
	if (twr_big_isequal(&a, &b)) return 0;
	if (twr_big_isgteq(&a, &b)) return 0;
	if (!twr_big_islteq(&a, &b)) return 0;
	if (!twr_big_isgteq(&b, &a)) return 0;

	twr_big_assign64u(&a, UINT64_MAX);
	twr_big_assign32u(&b, 0);
	twr_big_mult(&c, &a, &b);
	if (!twr_big_iszero(&c)) return 0;

	twr_big_bmax(&b);
	if (!twr_big_mult32u(&c, &b, 2)) return 0;

	twr_big_assign64u(&b, UINT64_MAX);
	twr_big_mult(&c, &a, &b);
	twr_big_assign128u(&a, 0xfffffffffffffffeULL, 0x0000000000000001ULL);
	if (!twr_big_isequal(&a, &c)) return 0;
	twr_big_2pow(&c, 51);
	twr_big_assign64u(&a, (uint64_t)1<<51);
	if (!twr_big_isequal(&a, &c)) return 0;
	twr_big_2pow(&c, 0);
	twr_big_assign32u(&a, 1);
	if (!twr_big_isequal(&a, &c)) return 0;
	twr_big_10pow(&c, 10, 9);
	twr_big_assign64u(&a, 1000000000);
	if (!twr_big_isequal(&a, &c)) return 0;

	twr_big_2pow(&a, 500);
	twr_big_10pow(&b, 2, 500);
	if (!twr_big_isequal(&a, &b)) return 0;

	twr_big_assign128u(&a, (uint64_t)0x0123456789ABCDEF, (uint64_t)0xFEDCBA9876543210);
	if (a.word[0]!=0x76543210) return 0;
	if (a.word[1]!=0xFEDCBA98) return 0;
	if (a.word[2]!=0x89ABCDEF) return 0;
	if (a.word[3]!=0x01234567) return 0;
	twr_big_assign128u(&a, 0, 0);
	if (!twr_big_iszero(&a)) return 0;


	twr_big_assign64u(&a, (uint64_t)0xFEDCBA9876543210);
	if (a.word[0]!=0x76543210) return 0;
	if (a.word[1]!=0xFEDCBA98) return 0;
	twr_big_assign64u(&a, 0);

	twr_big_bmax(&b);
	twr_big_bzero(&a);
	twr_big_assign(&a, &b);
	twr_big_add32u(&a, &a, 1);
	if (!twr_big_iszero(&a)) return 0;

	twr_big_10pow(&a, 10, 250);
	twr_big_assign(&b, &a);
	if (twr_big_shiftleft_words(&a, 7)) return 0;
	if (twr_big_shiftleft_bits(&b, 7*32)) return 0;
	if (!twr_big_isequal(&a, &b)) return 0;

	twr_big_assign32u(&a, 8);
	if (twr_big_get_bit(&a,	3)!=1) return 0;
	if (twr_big_get_bit(&a,	2)!=0) return 0;
	if (twr_big_get_bit(&a,	4)!=0) return 0;
	twr_big_set_bit(&a,	3, 0);
	if (twr_big_get_bit(&a,	3)!=0) return 0;

	twr_big_assign64u(&a, (uint64_t)0x8000000000000000);
	if (twr_big_get_bit(&a,	63)!=1) return 0;
	if (twr_big_get_bit(&a,	64)!=0) return 0;
	if (twr_big_get_bit(&a,	62)!=0) return 0;
	twr_big_set_bit(&a,	63, 0);
	if (twr_big_get_bit(&a,	63)!=0) return 0;

	twr_big_assign32u(&a, 1);
	twr_big_shiftleft_bits(&a, BIG_INT_WORD_COUNT*32-1);
	if (twr_big_get_bit(&a, BIG_INT_WORD_COUNT*32-1)!=1) return 0;
	if (twr_big_get_bit(&a, BIG_INT_WORD_COUNT*32-2)!=0) return 0;
	twr_big_set_bit(&a, BIG_INT_WORD_COUNT*32-1, 0);
	if (twr_big_get_bit(&a, BIG_INT_WORD_COUNT*32-1)!=0) return 0;

	twr_big_10pow(&a, 10, 123);
	twr_big_10pow(&b, 10, 123);
	twr_big_add(&c, &a, &b);  
	twr_big_sub(&a, &a, &b);
	if (!twr_big_iszero(&a)) return 0;
	twr_big_assign32u(&a, 2);
	twr_big_mult(&a, &b, &a);
	if (!(twr_big_isequal(&a, &c))) return 0;

	twr_big_bzero(&a);
	twr_big_assign32u(&b, 1);
	twr_big_sub(&a, &a, &b);

	twr_big_bmax(&b);
	if (!twr_big_isequal(&a, &b)) return 0;

	twr_big_assign32u(&a, 2);
	twr_big_assign32u(&b, 1);
	twr_big_sub(&c, &b, &a);
	twr_big_bmax(&b);
	if (!twr_big_isequal(&c, &b)) return 0;


	struct twr_bigint q,r;
	twr_big_assign32u(&a, 8);
	twr_big_assign32u(&b, 2);
	twr_big_assign32u(&c, 4);
	twr_big_div(&q, &r, &a, &b);
	if (!twr_big_isequal(&q, &c)) return 0;
	if (!twr_big_iszero(&r)) return 0;

	twr_big_10pow(&a, 10, 150);
	twr_big_10pow(&b, 10, 50);
	twr_big_add32u(&a, &a, 1);
	twr_big_div(&q, &r, &a, &b);
	twr_big_10pow(&c, 10, 100);
	if (!twr_big_isequal(&q, &c)) return 0;
	twr_big_assign32u(&c, 1);
	if (!twr_big_isequal(&r, &c)) return 0;

	struct twr_bigint num, den;
	twr_big_assign32u(&den, 1);
	twr_big_assign32u(&num, 1);
	if (0!=twr_big_10log(&num, &den)) return 0;

	twr_big_assign32u(&num, 9);
	if (0!=twr_big_10log(&num, &den)) return 0;

	twr_big_assign32u(&num, 10);
	if (1!=twr_big_10log(&num, &den)) return 0;

	twr_big_assign32u(&den, 9);
	twr_big_assign32u(&num, 1);
	if (-1!=twr_big_10log(&num, &den)) return 0;

	twr_big_assign32u(&den, 10);
	if (-1!=twr_big_10log(&num, &den)) return 0;

	twr_big_bmax(&num);
	twr_big_bmax(&den);
	if (0!=twr_big_10log(&num, &den)) return 0;

	twr_big_assign32u(&num, 1);
	int xx=twr_big_10log(&num, &den);
	if (-617 != xx) return 0;

	twr_big_assign32u(&den, 1);
	twr_big_bmax(&num);
	xx=twr_big_10log(&num, &den);
	if (616 != xx) return 0;


	twr_big_assign32u(&den, 1);
	twr_big_assign32u(&num, 1);
	if (0!=twr_big_2log(&num, &den)) return 0;

	twr_big_assign32u(&num, 2);
	if (1!=twr_big_2log(&num, &den)) return 0;

	twr_big_assign32u(&num, 3);
	if (1!=twr_big_2log(&num, &den)) return 0;

	twr_big_assign32u(&den, 1<<1);
	twr_big_assign32u(&num, 1);
	if (-1!=twr_big_2log(&num, &den)) return 0;

	twr_big_assign32u(&den, 3);
	if (-2!=twr_big_2log(&num, &den)) return 0;

	twr_big_assign64u(&den, 1ULL<<63);
	if (-63!=twr_big_2log(&num, &den)) return 0;

	twr_big_bmax(&num);
	twr_big_bmax(&den);
	if (0!=twr_big_2log(&num, &den)) return 0;

	twr_big_assign32u(&num, 1);
	if (-(BIG_INT_WORD_COUNT*32) != twr_big_2log(&num, &den)) return 0;

	twr_big_assign32u(&den, 1);
	twr_big_bmax(&num);
	if ((BIG_INT_WORD_COUNT*32-1) != twr_big_2log(&num, &den)) return 0;

	return 1;

	
}
