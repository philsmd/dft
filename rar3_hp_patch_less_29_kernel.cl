/**
 * Author......: See docs/credits.txt
 * License.....: MIT
 */

#ifdef KERNEL_STATIC
#include "inc_vendor.h"
#include "inc_types.h"
#include "inc_platform.cl"
#include "inc_common.cl"
#include "inc_hash_sha1.cl"
#include "inc_cipher_aes.cl"
#endif

#define COMPARE_S "inc_comp_single.cl"
#define COMPARE_M "inc_comp_multi.cl"

#define ROUNDS 0x40000

typedef struct pbkdf2_sha1
{
  u32 salt_buf[64];

} pbkdf2_sha1_t;

typedef struct rar3_tmp
{
  u32 dgst[5];

  u32 w[66]; // 256 byte pass + 8 byte salt

  u32 iv[4];

} rar3_tmp_t;

DECLSPEC void memcat8c_be (u32 *w0, u32 *w1, u32 *w2, u32 *w3, const u32 len, const u32 append, u32 *digest)
{
  const u32 func_len = len & 63;

  //const u32 mod = func_len & 3;
  const u32 div = func_len / 4;

  u32 tmp0;
  u32 tmp1;

  #if defined IS_AMD || defined IS_GENERIC
  tmp0 = hc_bytealign_be (0, append, func_len);
  tmp1 = hc_bytealign_be (append, 0, func_len);
  #endif

  #ifdef IS_NV
  const int selector = (0x76543210 >> ((func_len & 3) * 4)) & 0xffff;

  tmp0 = hc_byte_perm (append, 0, selector);
  tmp1 = hc_byte_perm (0, append, selector);
  #endif

  u32 carry = 0;

  switch (div)
  {
    case  0:  w0[0] |= tmp0;
              w0[1]  = tmp1;
              break;
    case  1:  w0[1] |= tmp0;
              w0[2]  = tmp1;
              break;
    case  2:  w0[2] |= tmp0;
              w0[3]  = tmp1;
              break;
    case  3:  w0[3] |= tmp0;
              w1[0]  = tmp1;
              break;
    case  4:  w1[0] |= tmp0;
              w1[1]  = tmp1;
              break;
    case  5:  w1[1] |= tmp0;
              w1[2]  = tmp1;
              break;
    case  6:  w1[2] |= tmp0;
              w1[3]  = tmp1;
              break;
    case  7:  w1[3] |= tmp0;
              w2[0]  = tmp1;
              break;
    case  8:  w2[0] |= tmp0;
              w2[1]  = tmp1;
              break;
    case  9:  w2[1] |= tmp0;
              w2[2]  = tmp1;
              break;
    case 10:  w2[2] |= tmp0;
              w2[3]  = tmp1;
              break;
    case 11:  w2[3] |= tmp0;
              w3[0]  = tmp1;
              break;
    case 12:  w3[0] |= tmp0;
              w3[1]  = tmp1;
              break;
    case 13:  w3[1] |= tmp0;
              w3[2]  = tmp1;
              break;
    case 14:  w3[2] |= tmp0;
              w3[3]  = tmp1;
              break;
    case 15:  w3[3] |= tmp0;
              carry  = tmp1;
              break;
  }

  const u32 new_len = func_len + 3;

  if (new_len >= 64)
  {
    sha1_transform (w0, w1, w2, w3, digest);

    w0[0] = carry;
    w0[1] = 0;
    w0[2] = 0;
    w0[3] = 0;
    w1[0] = 0;
    w1[1] = 0;
    w1[2] = 0;
    w1[3] = 0;
    w2[0] = 0;
    w2[1] = 0;
    w2[2] = 0;
    w2[3] = 0;
    w3[0] = 0;
    w3[1] = 0;
    w3[2] = 0;
    w3[3] = 0;
  }
}

KERNEL_FQ void m12500_init (KERN_ATTR_TMPS_ESALT (rar3_tmp_t, pbkdf2_sha1_t))
{
  /**
   * base
   */

  const u64 gid = get_global_id (0);

  if (gid >= gid_max) return;

  tmps[gid].dgst[0] = SHA1M_A;
  tmps[gid].dgst[1] = SHA1M_B;
  tmps[gid].dgst[2] = SHA1M_C;
  tmps[gid].dgst[3] = SHA1M_D;
  tmps[gid].dgst[4] = SHA1M_E;

  // store pass and salt in tmps:

  const u32 pw_len = pws[gid].pw_len;

  // first set the utf16le pass:

  u32 w[80] = { 0 };

  for (u32 i = 0, j = 0, k = 0; i < pw_len; i += 16, j += 4, k += 8)
  {
    u32 a[4];

    a[0] = pws[gid].i[j + 0];
    a[1] = pws[gid].i[j + 1];
    a[2] = pws[gid].i[j + 2];
    a[3] = pws[gid].i[j + 3];

    u32 b[4];
    u32 c[4];

    make_utf16le (a, b, c);

    w[k + 0] = hc_swap32_S (b[0]);
    w[k + 1] = hc_swap32_S (b[1]);
    w[k + 2] = hc_swap32_S (b[2]);
    w[k + 3] = hc_swap32_S (b[3]);
    w[k + 4] = hc_swap32_S (c[0]);
    w[k + 5] = hc_swap32_S (c[1]);
    w[k + 6] = hc_swap32_S (c[2]);
    w[k + 7] = hc_swap32_S (c[3]);
  }

  // append salt:

  const u32 salt_idx = (pw_len * 2) / 4;
  const u32 salt_off = (pw_len * 2) & 3;

  u32 salt_buf[3];

  salt_buf[0] = hc_swap32_S (salt_bufs[salt_pos].salt_buf[0]); // swap needed due to -O kernel
  salt_buf[1] = hc_swap32_S (salt_bufs[salt_pos].salt_buf[1]);
  salt_buf[2] = 0;

  // switch buffer by offset (can only be 0 or 2 because of utf16):

  if (salt_off == 2) // or just: if (salt_off)
  {
    salt_buf[2] = (salt_buf[1] << 16);
    salt_buf[1] = (salt_buf[1] >> 16) | (salt_buf[0] << 16);
    salt_buf[0] = (salt_buf[0] >> 16);
  }

  w[salt_idx] |= salt_buf[0];

  w[salt_idx + 1] = salt_buf[1];
  w[salt_idx + 2] = salt_buf[2];

  // store initial w[] (pass and salt) in tmps:

  for (u32 i = 0; i < 66; i++)
  {
    tmps[gid].w[i] = w[i];
  }

  // iv:

  tmps[gid].iv[0] = 0;
  tmps[gid].iv[1] = 0;
  tmps[gid].iv[2] = 0;
  tmps[gid].iv[3] = 0;
}

KERNEL_FQ void m12500_loop (KERN_ATTR_TMPS_ESALT (rar3_tmp_t, pbkdf2_sha1_t))
{
  const u64 gid = get_global_id (0);

  if (gid >= gid_max) return;

  /**
   * base
   */

  const u32 pw_len = pws[gid].pw_len;

  const u32 salt_len = 8;

  const u32 pw_salt_len = (pw_len * 2) + salt_len;

  const u32 p3 = pw_salt_len + 3;

  u32 w[80] = { 0 }; // 64 byte aligned

  for (u32 i = 0; i < 66; i++)
  {
    w[i] = tmps[gid].w[i];
  }

  // update IV:

  const u32 init_pos = loop_pos / (ROUNDS / 16);

  sha1_ctx_t ctx_iv;

  sha1_init (&ctx_iv);

  ctx_iv.h[0] = tmps[gid].dgst[0];
  ctx_iv.h[1] = tmps[gid].dgst[1];
  ctx_iv.h[2] = tmps[gid].dgst[2];
  ctx_iv.h[3] = tmps[gid].dgst[3];
  ctx_iv.h[4] = tmps[gid].dgst[4];

  ctx_iv.len = loop_pos * p3;

  sha1_update (&ctx_iv, w, pw_salt_len);

  memcat8c_be (ctx_iv.w0, ctx_iv.w1, ctx_iv.w2, ctx_iv.w3, ctx_iv.len, hc_swap32_S (loop_pos), ctx_iv.h);

  ctx_iv.len += 3;


  // copy the context from ctx_iv to ctx:

  sha1_ctx_t ctx;

  ctx.h[0] = ctx_iv.h[0];
  ctx.h[1] = ctx_iv.h[1];
  ctx.h[2] = ctx_iv.h[2];
  ctx.h[3] = ctx_iv.h[3];
  ctx.h[4] = ctx_iv.h[4];

  ctx.w0[0] = ctx_iv.w0[0];
  ctx.w0[1] = ctx_iv.w0[1];
  ctx.w0[2] = ctx_iv.w0[2];
  ctx.w0[3] = ctx_iv.w0[3];

  ctx.w1[0] = ctx_iv.w1[0];
  ctx.w1[1] = ctx_iv.w1[1];
  ctx.w1[2] = ctx_iv.w1[2];
  ctx.w1[3] = ctx_iv.w1[3];

  ctx.w2[0] = ctx_iv.w2[0];
  ctx.w2[1] = ctx_iv.w2[1];
  ctx.w2[2] = ctx_iv.w2[2];
  ctx.w2[3] = ctx_iv.w2[3];

  ctx.w3[0] = ctx_iv.w3[0];
  ctx.w3[1] = ctx_iv.w3[1];
  ctx.w3[2] = ctx_iv.w3[2];
  ctx.w3[3] = ctx_iv.w3[3];

  ctx.len = p3; // or ctx_iv.len ?

  // final () for the IV byte:

  sha1_final (&ctx_iv);

  const u32 iv_idx = init_pos / 4;
  const u32 iv_off = init_pos & 3;

  tmps[gid].iv[iv_idx] |= (ctx_iv.h[4] & 0xff) << (iv_off << 3);

  // main loop:

  for (u32 i = 0, j = (loop_pos + 1); i < 16383; i++, j++)
  {
    sha1_update (&ctx, w, pw_salt_len);

    memcat8c_be (ctx.w0, ctx.w1, ctx.w2, ctx.w3, ctx.len, hc_swap32_S (j), ctx.h);

    ctx.len += 3;
  }

  tmps[gid].dgst[0] = ctx.h[0];
  tmps[gid].dgst[1] = ctx.h[1];
  tmps[gid].dgst[2] = ctx.h[2];
  tmps[gid].dgst[3] = ctx.h[3];
  tmps[gid].dgst[4] = ctx.h[4];
}

KERNEL_FQ void m12500_comp (KERN_ATTR_TMPS_ESALT (rar3_tmp_t, pbkdf2_sha1_t))
{
  const u64 gid = get_global_id (0);
  const u64 lid = get_local_id (0);
  const u64 lsz = get_local_size (0);

  /**
   * aes shared
   */

  #ifdef REAL_SHM

  LOCAL_VK u32 s_td0[256];
  LOCAL_VK u32 s_td1[256];
  LOCAL_VK u32 s_td2[256];
  LOCAL_VK u32 s_td3[256];
  LOCAL_VK u32 s_td4[256];

  LOCAL_VK u32 s_te0[256];
  LOCAL_VK u32 s_te1[256];
  LOCAL_VK u32 s_te2[256];
  LOCAL_VK u32 s_te3[256];
  LOCAL_VK u32 s_te4[256];

  for (u32 i = lid; i < 256; i += lsz)
  {
    s_td0[i] = td0[i];
    s_td1[i] = td1[i];
    s_td2[i] = td2[i];
    s_td3[i] = td3[i];
    s_td4[i] = td4[i];

    s_te0[i] = te0[i];
    s_te1[i] = te1[i];
    s_te2[i] = te2[i];
    s_te3[i] = te3[i];
    s_te4[i] = te4[i];
  }

  SYNC_THREADS ();

  #else

  CONSTANT_AS u32a *s_td0 = td0;
  CONSTANT_AS u32a *s_td1 = td1;
  CONSTANT_AS u32a *s_td2 = td2;
  CONSTANT_AS u32a *s_td3 = td3;
  CONSTANT_AS u32a *s_td4 = td4;

  CONSTANT_AS u32a *s_te0 = te0;
  CONSTANT_AS u32a *s_te1 = te1;
  CONSTANT_AS u32a *s_te2 = te2;
  CONSTANT_AS u32a *s_te3 = te3;
  CONSTANT_AS u32a *s_te4 = te4;

  #endif

  if (gid >= gid_max) return;

  /**
   * base
   */

  const u32 pw_len = pws[gid].pw_len;

  const u32 salt_len = 8;

  const u32 pw_salt_len = (pw_len * 2) + salt_len;

  const u32 p3 = pw_salt_len + 3;

  u32 h[5];

  h[0] = tmps[gid].dgst[0];
  h[1] = tmps[gid].dgst[1];
  h[2] = tmps[gid].dgst[2];
  h[3] = tmps[gid].dgst[3];
  h[4] = tmps[gid].dgst[4];

  u32 w0[4];
  u32 w1[4];
  u32 w2[4];
  u32 w3[4];

  w0[0] = 0x80000000;
  w0[1] = 0;
  w0[2] = 0;
  w0[3] = 0;
  w1[0] = 0;
  w1[1] = 0;
  w1[2] = 0;
  w1[3] = 0;
  w2[0] = 0;
  w2[1] = 0;
  w2[2] = 0;
  w2[3] = 0;
  w3[0] = 0;
  w3[1] = 0;
  w3[2] = 0;
  w3[3] = (ROUNDS * p3) * 8;

  sha1_transform (w0, w1, w2, w3, h);

  u32 ukey[4];

  ukey[0] = hc_swap32_S (h[0]);
  ukey[1] = hc_swap32_S (h[1]);
  ukey[2] = hc_swap32_S (h[2]);
  ukey[3] = hc_swap32_S (h[3]);

  u32 ks[44];

  AES128_set_decrypt_key (ks, ukey, s_te0, s_te1, s_te2, s_te3, s_td0, s_td1, s_td2, s_td3);

  u32 data[4];

  data[0] = salt_bufs[salt_pos].salt_buf[2];
  data[1] = salt_bufs[salt_pos].salt_buf[3];
  data[2] = salt_bufs[salt_pos].salt_buf[4];
  data[3] = salt_bufs[salt_pos].salt_buf[5];

  u32 out[4];

  AES128_decrypt (ks, data, out, s_td0, s_td1, s_td2, s_td3, s_td4);

  u32 iv[2];

  iv[0] = tmps[gid].iv[0];
  iv[1] = tmps[gid].iv[1];

  out[0] ^= hc_swap32_S (iv[0]);
  out[1] ^= hc_swap32_S (iv[1]);

  const u32 r0 = out[0];
  const u32 r1 = out[1];
  const u32 r2 = 0;
  const u32 r3 = 0;

  #define il_pos 0

  #ifdef KERNEL_STATIC
  #include COMPARE_M
  #endif
}
