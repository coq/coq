/************************************************************************/
/*         *   The Coq Proof Assistant / The Coq Development Team       */
/*         *              and OCaml / The OCaml Development Team        */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/

#include <string.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/misc.h>

/* Caml_inline exists since 4.11 */
#ifndef Caml_inline
#if defined(_MSC_VER) && !defined(__cplusplus)
#define Caml_inline static __inline
#else
#define Caml_inline static inline
#endif
#endif

/* Mostly copied from ocaml extern.c (marshal implementation).
   Usually where we say analyse_foo it was called extern_foo in extern.c.
*/

/* stack for pending values to analyse */

#define ANALYSE_STACK_INIT_SIZE 256
#define ANALYSE_STACK_MAX_SIZE (1024*1024*100)

struct analyse_item { volatile value * v; volatile value * descr; mlsize_t count; int constant_descr; };

/* Hash table to record already-analysed values and their positions */

struct object_position { value obj; uintnat pos; };

/* The hash table uses open addressing, linear probing, and a redundant
   representation:
   - a bitvector [present] records which entries of the table are occupied;
   - an array [entries] records (object, position) pairs for the entries
     that are occupied.
   The bitvector is much smaller than the array (1/128th on 64-bit
   platforms, 1/64th on 32-bit platforms), so it has better locality,
   making it faster to determine that an object is not in the table.
   Also, it makes it faster to empty or initialize a table: only the
   [present] bitvector needs to be filled with zeros, the [entries]
   array can be left uninitialized.
*/

struct position_table {
  int shift;
  mlsize_t size;                    /* size == 1 << (wordsize - shift) */
  mlsize_t mask;                    /* mask == size - 1 */
  mlsize_t threshold;               /* threshold == a fixed fraction of size */
  uintnat * present;                /* [Bitvect_size(size)] */
  struct object_position * entries; /* [size]  */
};

/* bit vectors */

#define Bits_word (8 * sizeof(uintnat))
#define Bitvect_size(n) (((n) + Bits_word - 1) / Bits_word)

Caml_inline uintnat bitvect_test(uintnat * bv, uintnat i)
{
  return bv[i / Bits_word] & ((uintnat) 1 << (i & (Bits_word - 1)));
}

Caml_inline void bitvect_set(uintnat * bv, uintnat i)
{
  bv[i / Bits_word] |= ((uintnat) 1 << (i & (Bits_word - 1)));
}

/* Size-ing data structures.  Chosen so that
   sizeof(struct trail_block) and sizeof(struct output_block)
   are slightly below 8Kb. */

#define SIZE_OUTPUT_BLOCK 8100

struct output_block {
  struct output_block * next;
  char * end;
  char data[SIZE_OUTPUT_BLOCK];
};

#define POS_TABLE_INIT_SIZE_LOG2 8
#define POS_TABLE_INIT_SIZE (1 << POS_TABLE_INIT_SIZE_LOG2)

struct analyse_state {
  uintnat obj_counter; /* number of objects analysed so far
                          (only the ones we care about, not intermediates) */

  /* pending stack */
  struct analyse_item analyse_stack_init[ANALYSE_STACK_INIT_SIZE];
  struct analyse_item * analyse_stack;
  struct analyse_item * analyse_stack_limit;

  /* hash table to record already analysed objects */
  uintnat pos_table_present_init[Bitvect_size(POS_TABLE_INIT_SIZE)];
  struct object_position pos_table_entries_init[POS_TABLE_INIT_SIZE];
  struct position_table pos_table;

  /* buffered output */
  char * analyse_ptr;
  char * analyse_limit;

  struct output_block * analyse_output_first;
  struct output_block * analyse_output_block;
};

static void init_analyse_stack(struct analyse_state* s)
{
  /* (Re)initialize the globals for next time around */
  s->analyse_stack = s->analyse_stack_init;
  s->analyse_stack_limit = s->analyse_stack + ANALYSE_STACK_INIT_SIZE;
}

static struct analyse_state* init_analyse_state (void)
{
  struct analyse_state* s;
  s = caml_stat_alloc(sizeof(struct analyse_state));

  s->obj_counter = 0;
  init_analyse_stack(s);

  return s;
}

/* Multiplicative Fibonacci hashing
   (Knuth, TAOCP vol 3, section 6.4, page 518).
   HASH_FACTOR is (sqrt(5) - 1) / 2 * 2^wordsize. */
#ifdef ARCH_SIXTYFOUR
#define HASH_FACTOR 11400714819323198486UL
#else
#define HASH_FACTOR 2654435769UL
#endif
#define Hash(v,shift) (((uintnat)(v) * HASH_FACTOR) >> (shift))

/* When the table becomes 2/3 full, its size is increased. */
#define Threshold(sz) (((sz) * 2) / 3)

static void analyse_init_position_table(struct analyse_state* s)
{
  s->pos_table.size = POS_TABLE_INIT_SIZE;
  s->pos_table.shift = 8 * sizeof(value) - POS_TABLE_INIT_SIZE_LOG2;
  s->pos_table.mask = POS_TABLE_INIT_SIZE - 1;
  s->pos_table.threshold = Threshold(POS_TABLE_INIT_SIZE);
  s->pos_table.present = s->pos_table_present_init;
  s->pos_table.entries = s->pos_table_entries_init;
  memset(s->pos_table_present_init, 0,
         Bitvect_size(POS_TABLE_INIT_SIZE) * sizeof(uintnat));

}

static intnat analyse_output_length(struct analyse_state* s)
{
  struct output_block * blk;
  intnat len = 0;

  for (blk = s->analyse_output_first; blk != NULL; blk = blk->next) {
    len += blk->end - blk->data;
  }
  return len;
}

static void analyse_free_stack(struct analyse_state* s)
{
  /* Free the stack if needed */
  if (s->analyse_stack != s->analyse_stack_init) {
    caml_stat_free(s->analyse_stack);
    init_analyse_stack(s);
  }
}

static void analyse_free_position_table(struct analyse_state* s)
{
  if (s->pos_table.present != s->pos_table_present_init) {
    caml_stat_free(s->pos_table.present);
    caml_stat_free(s->pos_table.entries);
    /* Protect against repeated calls to analyse_free_position_table */
    s->pos_table.present = s->pos_table_present_init;
    s->pos_table.entries = s->pos_table_entries_init;
  }
}

static void free_analyse_output(struct analyse_state* s)
{
  struct output_block * blk, * nextblk;

  for(blk = s->analyse_output_first; blk != NULL; blk = nextblk) {
    nextblk = blk->next;
    caml_stat_free(blk);
  }
  analyse_free_stack(s);
  analyse_free_position_table(s);
}

CAMLnoreturn_start static void analyse_out_of_memory(struct analyse_state* s);
CAMLnoreturn_end

static void analyse_out_of_memory(struct analyse_state* s)
{
  free_analyse_output(s);
  caml_raise_out_of_memory();
}

CAMLnoreturn_start static void analyse_invalid_argument(struct analyse_state* s, char *msg);
CAMLnoreturn_end

static void analyse_invalid_argument(struct analyse_state* s, char *msg)
{
  free_analyse_output(s);
  caml_invalid_argument(msg);
}

static struct analyse_item * analyse_resize_stack(struct analyse_state* s,
                                                struct analyse_item * sp)
{
  asize_t newsize = 2 * (s->analyse_stack_limit - s->analyse_stack);
  asize_t sp_offset = sp - s->analyse_stack;
  struct analyse_item * newstack;

  if (newsize >= ANALYSE_STACK_MAX_SIZE) analyse_out_of_memory(s);
  newstack = caml_stat_calloc_noexc(newsize, sizeof(struct analyse_item));
  if (newstack == NULL) analyse_out_of_memory(s);

  /* Copy items from the old stack to the new stack */
  memcpy (newstack, s->analyse_stack,
          sizeof(struct analyse_item) * sp_offset);

  /* Free the old stack if it is not the initial stack */
  if (s->analyse_stack != s->analyse_stack_init)
    caml_stat_free(s->analyse_stack);

  s->analyse_stack = newstack;
  s->analyse_stack_limit = newstack + newsize;
  return newstack + sp_offset;
}

static void analyse_resize_position_table(struct analyse_state *s)
{
  mlsize_t new_size, new_byte_size;
  int new_shift;
  uintnat * new_present;
  struct object_position * new_entries;
  uintnat i, h;
  struct position_table old = s->pos_table;

  /* Grow the table quickly (x 8) up to 10^6 entries,
     more slowly (x 2) afterwards. */
  if (old.size < 1000000) {
    new_size = 8 * old.size;
    new_shift = old.shift - 3;
  } else {
    new_size = 2 * old.size;
    new_shift = old.shift - 1;
  }
  if (new_size == 0
      || caml_umul_overflow(new_size, sizeof(struct object_position),
                            &new_byte_size))
    analyse_out_of_memory(s);
  new_entries = caml_stat_alloc_noexc(new_byte_size);
  if (new_entries == NULL) analyse_out_of_memory(s);
  new_present =
    caml_stat_calloc_noexc(Bitvect_size(new_size), sizeof(uintnat));
  if (new_present == NULL) {
    caml_stat_free(new_entries);
    analyse_out_of_memory(s);
  }
  s->pos_table.size = new_size;
  s->pos_table.shift = new_shift;
  s->pos_table.mask = new_size - 1;
  s->pos_table.threshold = Threshold(new_size);
  s->pos_table.present = new_present;
  s->pos_table.entries = new_entries;

  /* Insert every entry of the old table in the new table */
  for (i = 0; i < old.size; i++) {
    if (! bitvect_test(old.present, i)) continue;
    h = Hash(old.entries[i].obj, s->pos_table.shift);
    while (bitvect_test(new_present, h)) {
      h = (h + 1) & s->pos_table.mask;
    }
    bitvect_set(new_present, h);
    new_entries[h] = old.entries[i];
  }

  /* Free the old tables if they are not the initial ones */
  if (old.present != s->pos_table_present_init) {
    caml_stat_free(old.present);
    caml_stat_free(old.entries);
  }
}

Caml_inline int analyse_lookup_position(struct analyse_state *s, value obj,
                                        uintnat * p_out, uintnat * h_out)
{
  uintnat h = Hash(obj, s->pos_table.shift);
  while (1) {
    if (! bitvect_test(s->pos_table.present, h)) {
      *h_out = h;
      return 0;
    }
    if (s->pos_table.entries[h].obj == obj) {
      *p_out = s->pos_table.entries[h].pos;
      return 1;
    }
    h = (h + 1) & s->pos_table.mask;
  }
}

/* Record the output position for the given object [obj]. */
/* The [h] parameter is the index in the hash table where the object
   must be inserted.  It was determined during lookup. */

static void analyse_record_location(struct analyse_state* s,
                                    value obj, uintnat h)
{
  bitvect_set(s->pos_table.present, h);
  s->pos_table.entries[h].obj = obj;
  s->pos_table.entries[h].pos = s->obj_counter;
  s->obj_counter++;
  if (s->obj_counter >= s->pos_table.threshold)
    analyse_resize_position_table(s);
}

static void init_analyse_output(struct analyse_state* s)
{
  s->analyse_output_first =
    caml_stat_alloc_noexc(sizeof(struct output_block));
  if (s->analyse_output_first == NULL) caml_raise_out_of_memory();
  s->analyse_output_block = s->analyse_output_first;
  s->analyse_output_block->next = NULL;
  s->analyse_ptr = s->analyse_output_block->data;
  s->analyse_limit = s->analyse_output_block->data + SIZE_OUTPUT_BLOCK;
}


static void grow_analyse_output(struct analyse_state* s, intnat required)
{
  struct output_block * blk;
  intnat extra;

  s->analyse_output_block->end = s->analyse_ptr;
  if (required <= SIZE_OUTPUT_BLOCK / 2)
    extra = 0;
  else
    extra = required;
  blk = caml_stat_alloc_noexc(sizeof(struct output_block) + extra);
  if (blk == NULL) analyse_out_of_memory(s);
  s->analyse_output_block->next = blk;
  s->analyse_output_block = blk;
  s->analyse_output_block->next = NULL;
  s->analyse_ptr = s->analyse_output_block->data;
  s->analyse_limit =
    s->analyse_output_block->data + SIZE_OUTPUT_BLOCK + extra;
}

Caml_inline void analyse_ensure_output(struct analyse_state* s, intnat howmuch)
{
  if (s->analyse_ptr + howmuch > s->analyse_limit) grow_analyse_output(s, howmuch);
}

Caml_inline void analyse_write_int(struct analyse_state* s, intnat i)
{
  intnat howmuch;
  for (howmuch = 1; howmuch <= 9; howmuch++) {
    if (i < (1 << (7 * howmuch))) {
      if (s->analyse_ptr + howmuch > s->analyse_limit) grow_analyse_output(s, howmuch);
      intnat j;
      for (j = 0; j < howmuch-1; j++) {
        s->analyse_ptr[j] = (i >> (7 * (howmuch - (j+1)))) | 0x80;
      }
      s->analyse_ptr[howmuch-1] = i & 0x7f;
      s->analyse_ptr += howmuch;
      return;
    }
  }
}

static void analyse_rec(struct analyse_state* s, value top_type_descr, value v)
{
  struct analyse_item * sp;
  uintnat h = 0;
  uintnat pos = 0;
  volatile value here_descr = top_type_descr;

  analyse_init_position_table(s);
  sp = s->analyse_stack;

  while(1) {
  loop_start: /* goto label instead of continue because of nesting in switch */
    if (Is_long(here_descr)) {
      switch (Int_val(here_descr)) {
      case 0: { /* Ignore */
        /* nothing to do */
        goto next_item;
      }
      default: {
        analyse_invalid_argument(s, "SharingAnalyser unknown constant type_descr");
      }
      }
    }
    else {
      /* TODO add asserts that the value matches the type_descr */
      header_t descr_hd = Hd_val(here_descr);
      tag_t descr_tag = Tag_hd(descr_hd);
      switch (descr_tag) {
      case 0: { /* Remember */
        if (analyse_lookup_position(s, v, &pos, &h)) {
          if (pos > s->obj_counter)
            analyse_invalid_argument (s, "sharingAnalyser found nonsense position");
          analyse_write_int(s, pos + 1);
          goto next_item;
        }
        else {
          analyse_write_int(s, 0);
          analyse_record_location(s, v, h);
          /* recurse on self using the sub descr */
          here_descr = Field(here_descr, 0);
          goto loop_start;
        }
      }
      case 1: { /* Array */
        if (Is_long(v)) {
          /* can empty array be encoded as 0? I forgot */
          goto next_item;
        }
        else {
          header_t hd = Hd_val(v);
          mlsize_t sz = Wosize_hd(hd);

          value * sub_descr = &Field(here_descr, 0);
          if (sz == 0) {
            goto next_item;
          }
          if (sz > 1) {
            /* remember to do the rest */
            sp++;
            if (sp >= s->analyse_stack_limit)
              sp = analyse_resize_stack(s, sp);
            sp->v = &Field(v,1);
            sp->descr = sub_descr;
            sp->count = sz - 1;
            sp->constant_descr = 1;
          }
          v = Field(v, 0);
          here_descr = *sub_descr;
          goto loop_start;
        }
      }
      case 2: { /* Sum */
        if (Is_long(v)) {
          /* Sum considers all constant constructors as Ignore */
          goto next_item;
        }
        else {
          header_t hd = Hd_val(v);
          tag_t tag = Tag_hd(hd);
          mlsize_t sz = Wosize_hd(hd);

          value this_tag_descrs = Field(Field(here_descr,0),tag);
          /* Remember that we still have to analyse fields 1 ... sz - 1 */
          if (sz > 1) {
            sp++;
            if (sp >= s->analyse_stack_limit)
              sp = analyse_resize_stack(s, sp);
            sp->v = &Field(v,1);
            sp->descr = &Field(this_tag_descrs,1);
            sp->count = sz - 1;
            sp->constant_descr = 0;
          }
          v = Field(v, 0);
          here_descr = Field(this_tag_descrs, 0);
          goto loop_start;
        }
      }
      case 3: { /* Proxy */
        here_descr = Field(here_descr, 0);
        goto loop_start;
      }
      default: {
        analyse_invalid_argument(s, "SharingAnalyser unknown type_descr");
      }
      }
    }

  next_item:
    /* Pop one more item to marshal, if any */
    if (sp == s->analyse_stack) {
      /* We are done.   Cleanup the stack and leave the function */
      analyse_free_stack(s);
      analyse_free_position_table(s);
      return;
    }
    here_descr = *(sp->descr);
    if (! sp->constant_descr) {
      (sp->descr)++;
    }
    v = *((sp->v)++);

    if (--(sp->count) == 0) sp--;
  }
  /* Never reached as function leaves with return */
}

static intnat analyse_value(struct analyse_state* s, value top_type_descr, value v) {
  /* main loop */
  analyse_rec(s, top_type_descr, v);
  /* record end of output */
  s->analyse_output_block->end = s->analyse_ptr;
  /* done */
  return analyse_output_length(s);
}

value coq_rec_analyse(value type_descr,value v) {
  intnat data_len, ofs;
  value res;
  struct output_block * blk, * nextblk;
  struct analyse_state* s = init_analyse_state();
  init_analyse_output(s);

  data_len = analyse_value(s, type_descr, v);
  blk = s->analyse_output_first;

  /* extern.c does not do this free, AFAICT the state is saved in te global Caml_state->extern_state */
  caml_stat_free(s);

  /* ALLOC! extern.c says we need to do the "blk = s->analyse_output_first" before this
     see also ocaml/ocaml#4030
   */
  res = caml_alloc_string(data_len);
  ofs = 0;
  while (blk != NULL) {
    intnat n = blk->end - blk->data;
    memcpy(&Byte(res, ofs), blk->data, n);
    ofs += n;
    nextblk = blk->next;
    caml_stat_free(blk);
    blk = nextblk;
  }
  return res;
}
