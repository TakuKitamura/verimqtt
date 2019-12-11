
Main_optimize.o:	file format Mach-O 64-bit x86-64

Disassembly of section __TEXT,__text:
_new_line:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:171
; {
       0:	48 8d 3d 00 00 00 00 	leaq	(%rip), %rdi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:172
; LowStar_Printf_print_string("\n");
       7:	e9 00 00 00 00 	jmp	0 <_new_line+0xc>
       c:	0f 1f 40 00 	nopl	(%rax)

_slice_byte:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:176
; {
      10:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:178
; if ((uint32_t)0U == (uint32_t)a)
      12:	40 84 f6 	testb	%sil, %sil
      15:	74 49 	je	73 <_slice_byte+0x50>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:180
; else if ((uint32_t)1U == (uint32_t)a)
      17:	83 e0 7f 	andl	$127, %eax
      1a:	40 80 fe 01 	cmpb	$1, %sil
      1e:	74 40 	je	64 <_slice_byte+0x50>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:182
; else if ((uint32_t)2U == (uint32_t)a)
      20:	89 f8 	movl	%edi, %eax
      22:	83 e0 3f 	andl	$63, %eax
      25:	40 80 fe 02 	cmpb	$2, %sil
      29:	74 35 	je	53 <_slice_byte+0x50>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:184
; else if ((uint32_t)3U == (uint32_t)a)
      2b:	89 f8 	movl	%edi, %eax
      2d:	83 e0 1f 	andl	$31, %eax
      30:	40 80 fe 03 	cmpb	$3, %sil
      34:	74 2a 	je	42 <_slice_byte+0x50>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:186
; else if ((uint32_t)4U == (uint32_t)a)
      36:	89 f8 	movl	%edi, %eax
      38:	83 e0 0f 	andl	$15, %eax
      3b:	40 80 fe 04 	cmpb	$4, %sil
      3f:	74 1f 	je	31 <_slice_byte+0x50>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:188
; else if ((uint32_t)5U == (uint32_t)a)
      41:	89 f8 	movl	%edi, %eax
      43:	83 e0 07 	andl	$7, %eax
      46:	40 80 fe 05 	cmpb	$5, %sil
      4a:	74 14 	je	20 <_slice_byte+0x50>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:190
; else if ((uint32_t)6U == (uint32_t)a)
      4c:	89 f9 	movl	%edi, %ecx
      4e:	83 e1 03 	andl	$3, %ecx
      51:	83 e7 01 	andl	$1, %edi
      54:	89 c8 	movl	%ecx, %eax
      56:	40 80 fe 06 	cmpb	$6, %sil
      5a:	0f 45 c7 	cmovnel	%edi, %eax
      5d:	0f 1f 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:194
; uint8_t for_mask_temp2;
      60:	80 fa 01 	cmpb	$1, %dl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:195
; if ((uint32_t)1U == (uint32_t)b)
      63:	74 43 	je	67 <_slice_byte+0x98>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:197
; else if ((uint32_t)2U == (uint32_t)b)
      65:	80 fa 02 	cmpb	$2, %dl
      68:	74 26 	je	38 <_slice_byte+0x80>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:199
; else if ((uint32_t)3U == (uint32_t)b)
      6a:	80 fa 03 	cmpb	$3, %dl
      6d:	74 59 	je	89 <_slice_byte+0xb8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:201
; else if ((uint32_t)4U == (uint32_t)b)
      6f:	80 fa 04 	cmpb	$4, %dl
      72:	74 4c 	je	76 <_slice_byte+0xb0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:203
; else if ((uint32_t)5U == (uint32_t)b)
      74:	80 fa 05 	cmpb	$5, %dl
      77:	74 67 	je	103 <_slice_byte+0xd0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:205
; else if ((uint32_t)6U == (uint32_t)b)
      79:	80 fa 06 	cmpb	$6, %dl
      7c:	74 6a 	je	106 <_slice_byte+0xd8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:207
; else if ((uint32_t)7U == (uint32_t)b)
      7e:	89 c1 	movl	%eax, %ecx
      80:	83 e1 fe 	andl	$-2, %ecx
      83:	80 fa 07 	cmpb	$7, %dl
      86:	0f 44 c1 	cmovel	%ecx, %eax
      89:	eb 08 	jmp	8 <_slice_byte+0x83>
      8b:	0f 1f 44 00 00 	nopl	(%rax,%rax)
      90:	83 e0 c0 	andl	$-64, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:211
; uint8_t mask = for_mask_temp1 & for_mask_temp2;
      93:	0f b6 c8 	movzbl	%al, %ecx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
      96:	b8 08 00 00 00 	movl	$8, %eax
      9b:	29 d0 	subl	%edx, %eax
      9d:	c4 e2 7a f7 c1 	sarxl	%eax, %ecx, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:213
; }
      a2:	c3 	retq
      a3:	0f 1f 44 00 00 	nopl	(%rax,%rax)
      a8:	83 e0 80 	andl	$-128, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:211
; uint8_t mask = for_mask_temp1 & for_mask_temp2;
      ab:	0f b6 c8 	movzbl	%al, %ecx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
      ae:	b8 08 00 00 00 	movl	$8, %eax
      b3:	29 d0 	subl	%edx, %eax
      b5:	c4 e2 7a f7 c1 	sarxl	%eax, %ecx, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:213
; }
      ba:	c3 	retq
      bb:	0f 1f 44 00 00 	nopl	(%rax,%rax)
      c0:	83 e0 f0 	andl	$-16, %eax
      c3:	eb ce 	jmp	-50 <_slice_byte+0x83>
      c5:	0f 1f 00 	nopl	(%rax)
      c8:	83 e0 e0 	andl	$-32, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:211
; uint8_t mask = for_mask_temp1 & for_mask_temp2;
      cb:	0f b6 c8 	movzbl	%al, %ecx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
      ce:	b8 08 00 00 00 	movl	$8, %eax
      d3:	29 d0 	subl	%edx, %eax
      d5:	c4 e2 7a f7 c1 	sarxl	%eax, %ecx, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:213
; }
      da:	c3 	retq
      db:	0f 1f 44 00 00 	nopl	(%rax,%rax)
      e0:	83 e0 f8 	andl	$-8, %eax
      e3:	eb ae 	jmp	-82 <_slice_byte+0x83>
      e5:	0f 1f 00 	nopl	(%rax)
      e8:	83 e0 fc 	andl	$-4, %eax
      eb:	eb a6 	jmp	-90 <_slice_byte+0x83>
      ed:	0f 1f 00 	nopl	(%rax)

_is_valid_decoding_packet_check:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:216
; {
      f0:	40 0f b6 c6 	movzbl	%sil, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
      f4:	44 0f b6 15 00 00 00 00 	movzbl	(%rip), %r10d
      fc:	44 0f b6 ce 	movzbl	%sil, %r9d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:220
; uint8_t ptr_status_v = ptr_status;
     100:	49 89 f8 	movq	%rdi, %r8
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     103:	31 d2 	xorl	%edx, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:233
; uint32_t data_length_minus_one = (uint32_t)(bytes_length - (uint8_t)1U);
     105:	ff c8 	decl	%eax
     107:	40 80 fe 01 	cmpb	$1, %sil
     10b:	74 33 	je	51 <_is_valid_decoding_packet_check+0x50>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:223
; if (i < bytes_length_u32)
     10d:	8d 4a 01 	leal	1(%rdx), %ecx
     110:	44 39 ca 	cmpl	%r9d, %edx
     113:	73 1b 	jae	27 <_is_valid_decoding_packet_check+0x40>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:225
; uint8_t decoding_packet = ptr_for_decoding_packets[i];
     115:	41 0f b6 30 	movzbl	(%r8), %esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:226
; if (bytes_length == (uint8_t)1U)
     119:	39 c2 	cmpl	%eax, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:234
; if (i == data_length_minus_one)
     11b:	74 4b 	je	75 <_is_valid_decoding_packet_check+0x78>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     11d:	40 84 f6 	testb	%sil, %sil
     120:	78 56 	js	86 <_is_valid_decoding_packet_check+0x88>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:240
; ptr_status = (uint8_t)3U;
     122:	b8 03 00 00 00 	movl	$3, %eax
     127:	c3 	retq
     128:	0f 1f 84 00 00 00 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:218
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     130:	83 f9 04 	cmpl	$4, %ecx
     133:	74 4b 	je	75 <_is_valid_decoding_packet_check+0x90>
     135:	49 ff c0 	incq	%r8
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:216
; {
     138:	89 ca 	movl	%ecx, %edx
     13a:	eb d1 	jmp	-47 <_is_valid_decoding_packet_check+0x1d>
     13c:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     140:	31 c0 	xorl	%eax, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:223
; if (i < bytes_length_u32)
     142:	8d 50 01 	leal	1(%rax), %edx
     145:	85 c0 	testl	%eax, %eax
     147:	74 11 	je	17 <_is_valid_decoding_packet_check+0x6a>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:218
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     149:	83 fa 04 	cmpl	$4, %edx
     14c:	74 24 	je	36 <_is_valid_decoding_packet_check+0x82>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     14e:	89 d0 	movl	%edx, %eax
     150:	48 ff c7 	incq	%rdi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:223
; if (i < bytes_length_u32)
     153:	8d 50 01 	leal	1(%rax), %edx
     156:	85 c0 	testl	%eax, %eax
     158:	75 ef 	jne	-17 <_is_valid_decoding_packet_check+0x59>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:225
; uint8_t decoding_packet = ptr_for_decoding_packets[i];
     15a:	80 3f 00 	cmpb	$0, (%rdi)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:228
; if (decoding_packet < (uint8_t)0U || decoding_packet > (uint8_t)127U)
     15d:	79 ef 	jns	-17 <_is_valid_decoding_packet_check+0x5e>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:229
; ptr_status = (uint8_t)1U;
     15f:	89 f0 	movl	%esi, %eax
     161:	c3 	retq
     162:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:236
; if (decoding_packet < (uint8_t)1U || decoding_packet > (uint8_t)127U)
     168:	40 84 f6 	testb	%sil, %sil
     16b:	7e 1b 	jle	27 <_is_valid_decoding_packet_check+0x98>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:218
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     16d:	83 f9 04 	cmpl	$4, %ecx
     170:	75 c3 	jne	-61 <_is_valid_decoding_packet_check+0x45>
     172:	31 c0 	xorl	%eax, %eax
     174:	c3 	retq
     175:	0f 1f 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     178:	41 38 f2 	cmpb	%sil, %r10b
     17b:	72 a5 	jb	-91 <_is_valid_decoding_packet_check+0x32>
     17d:	eb ee 	jmp	-18 <_is_valid_decoding_packet_check+0x7d>
     17f:	90 	nop
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:218
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     180:	31 c0 	xorl	%eax, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:246
; }
     182:	c3 	retq
     183:	0f 1f 44 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:237
; ptr_status = (uint8_t)2U;
     188:	b8 02 00 00 00 	movl	$2, %eax
     18d:	c3 	retq
     18e:	66 90 	nop

_most_significant_four_bit_to_zero:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:249
; {
     190:	8d 47 80 	leal	-128(%rdi), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:251
; return i - (uint8_t)128U;
     193:	40 84 ff 	testb	%dil, %dil
     196:	0f 49 c7 	cmovnsl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:254
; }
     199:	c3 	retq
     19a:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)

_except_most_significant_four_bit_to_zero:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:257
; {
     1a0:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:261
; return (uint8_t)128U;
     1a2:	83 e0 80 	andl	$-128, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:262
; }
     1a5:	c3 	retq
     1a6:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

_decodeing_variable_bytes:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:265
; {
     1b0:	40 0f b6 d6 	movzbl	%sil, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:220
; uint8_t ptr_status_v = ptr_status;
     1b4:	44 0f b6 15 00 00 00 00 	movzbl	(%rip), %r10d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     1bc:	48 89 f9 	movq	%rdi, %rcx
     1bf:	31 c0 	xorl	%eax, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:233
; uint32_t data_length_minus_one = (uint32_t)(bytes_length - (uint8_t)1U);
     1c1:	44 8d 42 ff 	leal	-1(%rdx), %r8d
     1c5:	40 80 fe 01 	cmpb	$1, %sil
     1c9:	74 45 	je	69 <_decodeing_variable_bytes+0x60>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:223
; if (i < bytes_length_u32)
     1cb:	8d 70 01 	leal	1(%rax), %esi
     1ce:	39 c2 	cmpl	%eax, %edx
     1d0:	76 26 	jbe	38 <_decodeing_variable_bytes+0x48>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:225
; uint8_t decoding_packet = ptr_for_decoding_packets[i];
     1d2:	44 0f b6 09 	movzbl	(%rcx), %r9d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:226
; if (bytes_length == (uint8_t)1U)
     1d6:	41 39 c0 	cmpl	%eax, %r8d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:234
; if (i == data_length_minus_one)
     1d9:	74 15 	je	21 <_decodeing_variable_bytes+0x40>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     1db:	45 84 c9 	testb	%r9b, %r9b
     1de:	78 58 	js	88 <_decodeing_variable_bytes+0x88>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:278
; return max_u32;
     1e0:	8b 05 00 00 00 00 	movl	(%rip), %eax
     1e6:	c3 	retq
     1e7:	66 0f 1f 84 00 00 00 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:236
; if (decoding_packet < (uint8_t)1U || decoding_packet > (uint8_t)127U)
     1f0:	45 84 c9 	testb	%r9b, %r9b
     1f3:	7e eb 	jle	-21 <_decodeing_variable_bytes+0x30>
     1f5:	0f 1f 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:218
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     1f8:	83 fe 04 	cmpl	$4, %esi
     1fb:	74 0b 	je	11 <_decodeing_variable_bytes+0x58>
     1fd:	48 ff c1 	incq	%rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:265
; {
     200:	89 f0 	movl	%esi, %eax
     202:	eb c7 	jmp	-57 <_decodeing_variable_bytes+0x1b>
     204:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:283
; uint8_t ptr_status_v = ptr_status;
     208:	0f b6 07 	movzbl	(%rdi), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:287
; uint8_t b_u8 = most_significant_four_bit_to_zero(decoding_packet);
     20b:	84 c0 	testb	%al, %al
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:250
; if (i >= (uint8_t)128U)
     20d:	78 31 	js	49 <_decodeing_variable_bytes+0x90>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:317
; }
     20f:	c3 	retq
     210:	ff c0 	incl	%eax
     212:	48 89 fa 	movq	%rdi, %rdx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:223
; if (i < bytes_length_u32)
     215:	83 f8 01 	cmpl	$1, %eax
     218:	74 0f 	je	15 <_decodeing_variable_bytes+0x79>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:218
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     21a:	83 f8 04 	cmpl	$4, %eax
     21d:	74 e9 	je	-23 <_decodeing_variable_bytes+0x58>
     21f:	ff c0 	incl	%eax
     221:	48 ff c2 	incq	%rdx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:223
; if (i < bytes_length_u32)
     224:	83 f8 01 	cmpl	$1, %eax
     227:	75 f1 	jne	-15 <_decodeing_variable_bytes+0x6a>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:225
; uint8_t decoding_packet = ptr_for_decoding_packets[i];
     229:	80 3a 00 	cmpb	$0, (%rdx)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:228
; if (decoding_packet < (uint8_t)0U || decoding_packet > (uint8_t)127U)
     22c:	79 f1 	jns	-15 <_decodeing_variable_bytes+0x6f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:278
; return max_u32;
     22e:	8b 05 00 00 00 00 	movl	(%rip), %eax
     234:	c3 	retq
     235:	0f 1f 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     238:	45 38 ca 	cmpb	%r9b, %r10b
     23b:	72 a3 	jb	-93 <_decodeing_variable_bytes+0x30>
     23d:	eb b9 	jmp	-71 <_decodeing_variable_bytes+0x48>
     23f:	90 	nop
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:251
; return i - (uint8_t)128U;
     240:	0f b6 57 01 	movzbl	1(%rdi), %edx
     244:	83 c0 80 	addl	$-128, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     247:	0f be c0 	movsbl	%al, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:289
; uint8_t b2_u8 = except_most_significant_four_bit_to_zero(decoding_packet);
     24a:	84 d2 	testb	%dl, %dl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:250
; if (i >= (uint8_t)128U)
     24c:	78 0a 	js	10 <_decodeing_variable_bytes+0xa8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     24e:	c1 e2 07 	shll	$7, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:297
; ptr_temp2 = ptr_temp1 + b_u32 * (uint32_t)128U;
     251:	01 d0 	addl	%edx, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:298
; ptr_for_remaining_length = ptr_temp2;
     253:	c3 	retq
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:284
; if (ptr_status_v == (uint8_t)1U)
     254:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:251
; return i - (uint8_t)128U;
     258:	83 c2 80 	addl	$-128, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     25b:	0f be d2 	movsbl	%dl, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:297
; ptr_temp2 = ptr_temp1 + b_u32 * (uint32_t)128U;
     25e:	c1 e2 07 	shll	$7, %edx
     261:	01 d0 	addl	%edx, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:298
; ptr_for_remaining_length = ptr_temp2;
     263:	0f b6 57 02 	movzbl	2(%rdi), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:287
; uint8_t b_u8 = most_significant_four_bit_to_zero(decoding_packet);
     267:	84 d2 	testb	%dl, %dl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:250
; if (i >= (uint8_t)128U)
     269:	78 0d 	js	13 <_decodeing_variable_bytes+0xc8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     26b:	c1 e2 0e 	shll	$14, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:302
; ptr_temp3 = ptr_temp2 + b_u32 * (uint32_t)128U * (uint32_t)128U;
     26e:	01 d0 	addl	%edx, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:303
; ptr_for_remaining_length = ptr_temp3;
     270:	c3 	retq
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:284
; if (ptr_status_v == (uint8_t)1U)
     271:	0f 1f 80 00 00 00 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:251
; return i - (uint8_t)128U;
     278:	83 c2 80 	addl	$-128, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:286
; uint8_t decoding_packet = ptr_for_decoding_packets[i];
     27b:	0f b6 77 03 	movzbl	3(%rdi), %esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     27f:	0f be d2 	movsbl	%dl, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:302
; ptr_temp3 = ptr_temp2 + b_u32 * (uint32_t)128U * (uint32_t)128U;
     282:	c1 e2 0e 	shll	$14, %edx
     285:	01 c2 	addl	%eax, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:303
; ptr_for_remaining_length = ptr_temp3;
     287:	8d 46 80 	leal	-128(%rsi), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     28a:	40 84 f6 	testb	%sil, %sil
     28d:	0f be c0 	movsbl	%al, %eax
     290:	0f 49 c6 	cmovnsl	%esi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:290
; if (i == (uint32_t)0U)
     293:	c1 e0 15 	shll	$21, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:307
; ptr_temp4 = ptr_temp3 + b_u32 * (uint32_t)128U * (uint32_t)128U * (uint32_t)128U;
     296:	01 d0 	addl	%edx, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:308
; ptr_for_remaining_length = ptr_temp4;
     298:	c3 	retq
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:317
; }
     299:	0f 1f 80 00 00 00 00 	nopl	(%rax)

_get_remaining_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:325
; {
     2a0:	40 0f b6 cf 	movzbl	%dil, %ecx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     2a4:	44 0f b6 1d 00 00 00 00 	movzbl	(%rip), %r11d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:326
; uint32_t fixed_value = packet_size - (uint32_t)1U;
     2ac:	ff ca 	decl	%edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:327
; uint32_t bytes_length_u32 = (uint32_t)bytes_length;
     2ae:	49 89 f0 	movq	%rsi, %r8
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     2b1:	31 c0 	xorl	%eax, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:233
; uint32_t data_length_minus_one = (uint32_t)(bytes_length - (uint8_t)1U);
     2b3:	44 8d 49 ff 	leal	-1(%rcx), %r9d
     2b7:	40 80 ff 01 	cmpb	$1, %dil
     2bb:	74 2d 	je	45 <_get_remaining_length+0x4a>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:223
; if (i < bytes_length_u32)
     2bd:	8d 78 01 	leal	1(%rax), %edi
     2c0:	39 c1 	cmpl	%eax, %ecx
     2c2:	76 44 	jbe	68 <_get_remaining_length+0x68>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:225
; uint8_t decoding_packet = ptr_for_decoding_packets[i];
     2c4:	45 0f b6 10 	movzbl	(%r8), %r10d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:226
; if (bytes_length == (uint8_t)1U)
     2c8:	41 39 c1 	cmpl	%eax, %r9d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:234
; if (i == data_length_minus_one)
     2cb:	74 33 	je	51 <_get_remaining_length+0x60>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     2cd:	45 84 d2 	testb	%r10b, %r10b
     2d0:	78 66 	js	102 <_get_remaining_length+0x98>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:278
; return max_u32;
     2d2:	8b 05 00 00 00 00 	movl	(%rip), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:329
; if (untrust_r != max_u32)
     2d8:	c3 	retq
     2d9:	0f 1f 80 00 00 00 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:218
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     2e0:	83 ff 04 	cmpl	$4, %edi
     2e3:	74 33 	je	51 <_get_remaining_length+0x78>
     2e5:	49 ff c0 	incq	%r8
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     2e8:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:223
; if (i < bytes_length_u32)
     2ea:	8d 78 01 	leal	1(%rax), %edi
     2ed:	85 c0 	testl	%eax, %eax
     2ef:	75 ef 	jne	-17 <_get_remaining_length+0x40>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:225
; uint8_t decoding_packet = ptr_for_decoding_packets[i];
     2f1:	41 80 38 00 	cmpb	$0, (%r8)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:228
; if (decoding_packet < (uint8_t)0U || decoding_packet > (uint8_t)127U)
     2f5:	79 ee 	jns	-18 <_get_remaining_length+0x45>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:278
; return max_u32;
     2f7:	8b 05 00 00 00 00 	movl	(%rip), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:329
; if (untrust_r != max_u32)
     2fd:	c3 	retq
     2fe:	66 90 	nop
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:236
; if (decoding_packet < (uint8_t)1U || decoding_packet > (uint8_t)127U)
     300:	45 84 d2 	testb	%r10b, %r10b
     303:	7e cd 	jle	-51 <_get_remaining_length+0x32>
     305:	0f 1f 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:218
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     308:	83 ff 04 	cmpl	$4, %edi
     30b:	74 0b 	je	11 <_get_remaining_length+0x78>
     30d:	49 ff c0 	incq	%r8
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:325
; {
     310:	89 f8 	movl	%edi, %eax
     312:	eb a9 	jmp	-87 <_get_remaining_length+0x1d>
     314:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:283
; uint8_t ptr_status_v = ptr_status;
     318:	0f b6 06 	movzbl	(%rsi), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:287
; uint8_t b_u8 = most_significant_four_bit_to_zero(decoding_packet);
     31b:	84 c0 	testb	%al, %al
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:250
; if (i >= (uint8_t)128U)
     31d:	78 21 	js	33 <_get_remaining_length+0xa0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:281
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     31f:	8b 35 00 00 00 00 	movl	(%rip), %esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:329
; if (untrust_r != max_u32)
     325:	39 c6 	cmpl	%eax, %esi
     327:	74 07 	je	7 <_get_remaining_length+0x90>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:330
; if (bytes_length_u32 + untrust_r == fixed_value)
     329:	01 c1 	addl	%eax, %ecx
     32b:	39 d1 	cmpl	%edx, %ecx
     32d:	0f 45 c6 	cmovnel	%esi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:336
; }
     330:	c3 	retq
     331:	0f 1f 80 00 00 00 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     338:	45 38 d3 	cmpb	%r10b, %r11b
     33b:	72 95 	jb	-107 <_get_remaining_length+0x32>
     33d:	eb c9 	jmp	-55 <_get_remaining_length+0x68>
     33f:	90 	nop
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:251
; return i - (uint8_t)128U;
     340:	0f b6 7e 01 	movzbl	1(%rsi), %edi
     344:	83 c0 80 	addl	$-128, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     347:	0f be c0 	movsbl	%al, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:289
; uint8_t b2_u8 = except_most_significant_four_bit_to_zero(decoding_packet);
     34a:	40 84 ff 	testb	%dil, %dil
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:250
; if (i >= (uint8_t)128U)
     34d:	78 11 	js	17 <_get_remaining_length+0xc0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     34f:	c1 e7 07 	shll	$7, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:297
; ptr_temp2 = ptr_temp1 + b_u32 * (uint32_t)128U;
     352:	01 f8 	addl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:298
; ptr_for_remaining_length = ptr_temp2;
     354:	eb c9 	jmp	-55 <_get_remaining_length+0x7f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:284
; if (ptr_status_v == (uint8_t)1U)
     356:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:251
; return i - (uint8_t)128U;
     360:	83 c7 80 	addl	$-128, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     363:	40 0f be ff 	movsbl	%dil, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:297
; ptr_temp2 = ptr_temp1 + b_u32 * (uint32_t)128U;
     367:	c1 e7 07 	shll	$7, %edi
     36a:	01 f8 	addl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:298
; ptr_for_remaining_length = ptr_temp2;
     36c:	0f b6 7e 02 	movzbl	2(%rsi), %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:287
; uint8_t b_u8 = most_significant_four_bit_to_zero(decoding_packet);
     370:	40 84 ff 	testb	%dil, %dil
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:250
; if (i >= (uint8_t)128U)
     373:	78 0b 	js	11 <_get_remaining_length+0xe0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     375:	c1 e7 0e 	shll	$14, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:302
; ptr_temp3 = ptr_temp2 + b_u32 * (uint32_t)128U * (uint32_t)128U;
     378:	01 f8 	addl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:303
; ptr_for_remaining_length = ptr_temp3;
     37a:	eb a3 	jmp	-93 <_get_remaining_length+0x7f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:284
; if (ptr_status_v == (uint8_t)1U)
     37c:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:251
; return i - (uint8_t)128U;
     380:	83 c7 80 	addl	$-128, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:286
; uint8_t decoding_packet = ptr_for_decoding_packets[i];
     383:	44 0f b6 46 03 	movzbl	3(%rsi), %r8d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     388:	40 0f be ff 	movsbl	%dil, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:302
; ptr_temp3 = ptr_temp2 + b_u32 * (uint32_t)128U * (uint32_t)128U;
     38c:	c1 e7 0e 	shll	$14, %edi
     38f:	01 c7 	addl	%eax, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:303
; ptr_for_remaining_length = ptr_temp3;
     391:	41 8d 40 80 	leal	-128(%r8), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     395:	45 84 c0 	testb	%r8b, %r8b
     398:	0f be c0 	movsbl	%al, %eax
     39b:	41 0f 49 c0 	cmovnsl	%r8d, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:290
; if (i == (uint32_t)0U)
     39f:	c1 e0 15 	shll	$21, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:307
; ptr_temp4 = ptr_temp3 + b_u32 * (uint32_t)128U * (uint32_t)128U * (uint32_t)128U;
     3a2:	01 f8 	addl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:308
; ptr_for_remaining_length = ptr_temp4;
     3a4:	e9 76 ff ff ff 	jmp	-138 <_get_remaining_length+0x7f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:310
; if (b2_u8 == (uint8_t)0U)
     3a9:	0f 1f 80 00 00 00 00 	nopl	(%rax)

_get_message_type:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:339
; {
     3b0:	8d 47 ff 	leal	-1(%rdi), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:341
; return max_u8;
     3b3:	3c 0e 	cmpb	$14, %al
     3b5:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     3bc:	0f 46 c7 	cmovbel	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:344
; }
     3bf:	c3 	retq

___proj__Mkstruct_flags__item__flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:347
; {
     3c0:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:349
; }
     3c2:	c3 	retq
     3c3:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     3cd:	0f 1f 00 	nopl	(%rax)

___proj__Mkstruct_flags__item__dup_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:352
; {
     3d0:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:353
; return projectee.dup_flag;
     3d2:	0f b6 c4 	movzbl	%ah, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:354
; }
     3d5:	c3 	retq
     3d6:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_flags__item__qos_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:357
; {
     3e0:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:358
; return projectee.qos_flag;
     3e2:	c1 e8 10 	shrl	$16, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:359
; }
     3e5:	c3 	retq
     3e6:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_flags__item__retain_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:362
; {
     3f0:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:363
; return projectee.retain_flag;
     3f2:	c1 e8 18 	shrl	$24, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:364
; }
     3f5:	c3 	retq
     3f6:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header_constant__item__message_type_constant:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:370
; {
     400:	0f b6 44 24 08 	movzbl	8(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:372
; }
     405:	c3 	retq
     406:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header_constant__item__message_name_constant:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:378
; {
     410:	48 8b 44 24 10 	movq	16(%rsp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:380
; }
     415:	c3 	retq
     416:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header_constant__item__flags_constant:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:386
; {
     420:	8b 44 24 18 	movl	24(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:388
; }
     424:	c3 	retq
     425:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     42f:	90 	nop

___proj__Mkstruct_variable_header_publish__item__topic_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:394
; {
     430:	8b 44 24 08 	movl	8(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:396
; }
     434:	c3 	retq
     435:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     43f:	90 	nop

___proj__Mkstruct_variable_header_publish__item__topic_name:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:402
; {
     440:	48 8b 44 24 10 	movq	16(%rsp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:404
; }
     445:	c3 	retq
     446:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_variable_header_publish__item__property_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:410
; {
     450:	8b 44 24 18 	movl	24(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:412
; }
     454:	c3 	retq
     455:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     45f:	90 	nop

___proj__Mkstruct_variable_header_publish__item__payload:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:418
; {
     460:	48 8b 44 24 20 	movq	32(%rsp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:420
; }
     465:	c3 	retq
     466:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_error_struct__item__code:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:423
; {
     470:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:425
; }
     472:	c3 	retq
     473:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     47d:	0f 1f 00 	nopl	(%rax)

___proj__Mkstruct_error_struct__item__message:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:428
; {
     480:	48 89 f0 	movq	%rsi, %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:430
; }
     483:	c3 	retq
     484:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     48e:	66 90 	nop

___proj__Mkstruct_fixed_header__item__message_type:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:433
; {
     490:	0f b6 44 24 08 	movzbl	8(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:435
; }
     495:	c3 	retq
     496:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header__item__message_name:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:438
; {
     4a0:	48 8b 44 24 10 	movq	16(%rsp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:440
; }
     4a5:	c3 	retq
     4a6:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header__item__flags:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:443
; {
     4b0:	8b 44 24 18 	movl	24(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:445
; }
     4b4:	c3 	retq
     4b5:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     4bf:	90 	nop

___proj__Mkstruct_fixed_header__item__remaining_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:448
; {
     4c0:	8b 44 24 1c 	movl	28(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:450
; }
     4c4:	c3 	retq
     4c5:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     4cf:	90 	nop

___proj__Mkstruct_fixed_header__item__publish:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:454
; {
     4d0:	c5 fa 6f 44 24 20 	vmovdqu	32(%rsp), %xmm0
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:455
; return projectee.publish;
     4d6:	c5 fa 6f 4c 24 30 	vmovdqu	48(%rsp), %xmm1
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:454
; {
     4dc:	48 89 f8 	movq	%rdi, %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:455
; return projectee.publish;
     4df:	c5 f8 11 07 	vmovups	%xmm0, (%rdi)
     4e3:	c5 f8 11 4f 10 	vmovups	%xmm1, 16(%rdi)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:456
; }
     4e8:	c3 	retq
     4e9:	0f 1f 80 00 00 00 00 	nopl	(%rax)

___proj__Mkstruct_fixed_header__item__error:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:459
; {
     4f0:	48 8b 54 24 48 	movq	72(%rsp), %rdx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:460
; return projectee.error;
     4f5:	48 8b 44 24 40 	movq	64(%rsp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:461
; }
     4fa:	c3 	retq
     4fb:	0f 1f 44 00 00 	nopl	(%rax,%rax)

___proj__Mkstruct_fixed_header_parts__item___fixed_header_first_one_byte:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:467
; {
     500:	0f b6 44 24 08 	movzbl	8(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:469
; }
     505:	c3 	retq
     506:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header_parts__item__is_searching_remaining_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:475
; {
     510:	0f b6 44 24 09 	movzbl	9(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:477
; }
     515:	c3 	retq
     516:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header_parts__item__is_searching_property_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:483
; {
     520:	0f b6 44 24 0a 	movzbl	10(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:485
; }
     525:	c3 	retq
     526:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header_parts__item___message_type:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:489
; {
     530:	0f b6 44 24 0b 	movzbl	11(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:491
; }
     535:	c3 	retq
     536:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header_parts__item___remaining_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:497
; {
     540:	8b 44 24 0c 	movl	12(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:499
; }
     544:	c3 	retq
     545:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     54f:	90 	nop

___proj__Mkstruct_fixed_header_parts__item___topic_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:503
; {
     550:	8b 44 24 10 	movl	16(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:505
; }
     554:	c3 	retq
     555:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     55f:	90 	nop

___proj__Mkstruct_fixed_header_parts__item___topic_name:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:509
; {
     560:	48 8b 44 24 18 	movq	24(%rsp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:511
; }
     565:	c3 	retq
     566:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header_parts__item___topic_name_error_status:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:517
; {
     570:	0f b6 44 24 20 	movzbl	32(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:519
; }
     575:	c3 	retq
     576:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header_parts__item___property_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:525
; {
     580:	8b 44 24 24 	movl	36(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:527
; }
     584:	c3 	retq
     585:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     58f:	90 	nop

___proj__Mkstruct_fixed_header_parts__item___payload:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:531
; {
     590:	48 8b 44 24 28 	movq	40(%rsp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:533
; }
     595:	c3 	retq
     596:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

___proj__Mkstruct_fixed_header_parts__item___payload_error_status:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:539
; {
     5a0:	0f b6 44 24 30 	movzbl	48(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:541
; }
     5a5:	c3 	retq
     5a6:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

_is_valid_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:544
; {
     5b0:	40 38 7c 24 18 	cmpb	%dil, 24(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:545
; return s.flags_constant.flag == flag;
     5b5:	0f 94 c0 	sete	%al
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:546
; }
     5b8:	c3 	retq
     5b9:	0f 1f 80 00 00 00 00 	nopl	(%rax)

_struct_fixed_publish:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:550
; {
     5c0:	48 89 f8 	movq	%rdi, %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:552
; (
     5c3:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     5ca:	40 88 70 11 	movb	%sil, 17(%rax)
     5ce:	40 88 38 	movb	%dil, (%rax)
     5d1:	48 8b 3d 00 00 00 00 	movq	(%rip), %rdi
     5d8:	88 50 12 	movb	%dl, 18(%rax)
     5db:	48 89 78 08 	movq	%rdi, 8(%rax)
     5df:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     5e6:	88 48 13 	movb	%cl, 19(%rax)
     5e9:	40 88 78 10 	movb	%dil, 16(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:564
; }
     5ed:	c3 	retq
     5ee:	66 90 	nop

_get_struct_fixed_header_constant_except_publish:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:568
; {
     5f0:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:569
; if (message_type == define_mqtt_control_packet_CONNECT)
     5f7:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:568
; {
     5fe:	48 89 f8 	movq	%rdi, %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:569
; if (message_type == define_mqtt_control_packet_CONNECT)
     601:	0f 84 c9 00 00 00 	je	201 <_get_struct_fixed_header_constant_except_publish+0xe0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:583
; else if (message_type == define_mqtt_control_packet_CONNACK)
     607:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     60e:	0f 84 34 01 00 00 	je	308 <_get_struct_fixed_header_constant_except_publish+0x158>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:597
; else if (message_type == define_mqtt_control_packet_PUBACK)
     614:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     61b:	0f 84 d7 00 00 00 	je	215 <_get_struct_fixed_header_constant_except_publish+0x108>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:611
; else if (message_type == define_mqtt_control_packet_PUBREC)
     621:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     628:	0f 84 42 01 00 00 	je	322 <_get_struct_fixed_header_constant_except_publish+0x180>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:625
; else if (message_type == define_mqtt_control_packet_PUBREL)
     62e:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     635:	0f 84 5d 01 00 00 	je	349 <_get_struct_fixed_header_constant_except_publish+0x1a8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:639
; else if (message_type == define_mqtt_control_packet_PUBCOMP)
     63b:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     642:	0f 84 78 01 00 00 	je	376 <_get_struct_fixed_header_constant_except_publish+0x1d0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:653
; else if (message_type == define_mqtt_control_packet_SUBSCRIBE)
     648:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     64f:	0f 84 cb 00 00 00 	je	203 <_get_struct_fixed_header_constant_except_publish+0x130>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:667
; else if (message_type == define_mqtt_control_packet_SUBACK)
     655:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     65c:	0f 84 ae 01 00 00 	je	430 <_get_struct_fixed_header_constant_except_publish+0x220>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:681
; else if (message_type == define_mqtt_control_packet_UNSUBSCRIBE)
     662:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     669:	0f 84 c9 01 00 00 	je	457 <_get_struct_fixed_header_constant_except_publish+0x248>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:695
; else if (message_type == define_mqtt_control_packet_UNSUBACK)
     66f:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     676:	40 38 ce 	cmpb	%cl, %sil
     679:	0f 84 e1 01 00 00 	je	481 <_get_struct_fixed_header_constant_except_publish+0x270>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:709
; else if (message_type == define_mqtt_control_packet_PINGREQ)
     67f:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     686:	0f 84 fc 01 00 00 	je	508 <_get_struct_fixed_header_constant_except_publish+0x298>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:723
; else if (message_type == define_mqtt_control_packet_PINGRESP)
     68c:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     693:	0f 84 17 02 00 00 	je	535 <_get_struct_fixed_header_constant_except_publish+0x2c0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:737
; else if (message_type == define_mqtt_control_packet_DISCONNECT)
     699:	40 38 35 00 00 00 00 	cmpb	%sil, (%rip)
     6a0:	0f 84 42 01 00 00 	je	322 <_get_struct_fixed_header_constant_except_publish+0x1f8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:752
; return
     6a6:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:753
; (
     6ad:	88 57 11 	movb	%dl, 17(%rdi)
     6b0:	88 0f 	movb	%cl, (%rdi)
     6b2:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
     6b9:	88 57 12 	movb	%dl, 18(%rdi)
     6bc:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     6c0:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     6c7:	88 57 13 	movb	%dl, 19(%rdi)
     6ca:	88 4f 10 	movb	%cl, 16(%rdi)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:765
; }
     6cd:	c3 	retq
     6ce:	66 90 	nop
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:570
; return
     6d0:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:571
; (
     6d7:	40 88 37 	movb	%sil, (%rdi)
     6da:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     6de:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     6e5:	88 57 11 	movb	%dl, 17(%rdi)
     6e8:	88 4f 10 	movb	%cl, 16(%rdi)
     6eb:	88 57 12 	movb	%dl, 18(%rdi)
     6ee:	88 57 13 	movb	%dl, 19(%rdi)
     6f1:	c3 	retq
     6f2:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:598
; return
     6f8:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:599
; (
     6ff:	40 88 37 	movb	%sil, (%rdi)
     702:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     706:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     70d:	88 57 11 	movb	%dl, 17(%rdi)
     710:	88 4f 10 	movb	%cl, 16(%rdi)
     713:	88 57 12 	movb	%dl, 18(%rdi)
     716:	88 57 13 	movb	%dl, 19(%rdi)
     719:	c3 	retq
     71a:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:654
; return
     720:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:655
; (
     727:	40 88 37 	movb	%sil, (%rdi)
     72a:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     72e:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     735:	88 57 11 	movb	%dl, 17(%rdi)
     738:	88 4f 10 	movb	%cl, 16(%rdi)
     73b:	88 57 12 	movb	%dl, 18(%rdi)
     73e:	88 57 13 	movb	%dl, 19(%rdi)
     741:	c3 	retq
     742:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:584
; return
     748:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:585
; (
     74f:	40 88 37 	movb	%sil, (%rdi)
     752:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     756:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     75d:	88 57 11 	movb	%dl, 17(%rdi)
     760:	88 4f 10 	movb	%cl, 16(%rdi)
     763:	88 57 12 	movb	%dl, 18(%rdi)
     766:	88 57 13 	movb	%dl, 19(%rdi)
     769:	c3 	retq
     76a:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:612
; return
     770:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:613
; (
     777:	40 88 37 	movb	%sil, (%rdi)
     77a:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     77e:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     785:	88 57 11 	movb	%dl, 17(%rdi)
     788:	88 4f 10 	movb	%cl, 16(%rdi)
     78b:	88 57 12 	movb	%dl, 18(%rdi)
     78e:	88 57 13 	movb	%dl, 19(%rdi)
     791:	c3 	retq
     792:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:626
; return
     798:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:627
; (
     79f:	40 88 37 	movb	%sil, (%rdi)
     7a2:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     7a6:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     7ad:	88 57 11 	movb	%dl, 17(%rdi)
     7b0:	88 4f 10 	movb	%cl, 16(%rdi)
     7b3:	88 57 12 	movb	%dl, 18(%rdi)
     7b6:	88 57 13 	movb	%dl, 19(%rdi)
     7b9:	c3 	retq
     7ba:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:640
; return
     7c0:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:641
; (
     7c7:	40 88 37 	movb	%sil, (%rdi)
     7ca:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     7ce:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     7d5:	88 57 11 	movb	%dl, 17(%rdi)
     7d8:	88 4f 10 	movb	%cl, 16(%rdi)
     7db:	88 57 12 	movb	%dl, 18(%rdi)
     7de:	88 57 13 	movb	%dl, 19(%rdi)
     7e1:	c3 	retq
     7e2:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:738
; return
     7e8:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:739
; (
     7ef:	40 88 37 	movb	%sil, (%rdi)
     7f2:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     7f6:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     7fd:	88 57 11 	movb	%dl, 17(%rdi)
     800:	88 4f 10 	movb	%cl, 16(%rdi)
     803:	88 57 12 	movb	%dl, 18(%rdi)
     806:	88 57 13 	movb	%dl, 19(%rdi)
     809:	c3 	retq
     80a:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:668
; return
     810:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:669
; (
     817:	40 88 37 	movb	%sil, (%rdi)
     81a:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     81e:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     825:	88 57 11 	movb	%dl, 17(%rdi)
     828:	88 4f 10 	movb	%cl, 16(%rdi)
     82b:	88 57 12 	movb	%dl, 18(%rdi)
     82e:	88 57 13 	movb	%dl, 19(%rdi)
     831:	c3 	retq
     832:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:682
; return
     838:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:683
; (
     83f:	40 88 37 	movb	%sil, (%rdi)
     842:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     846:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     84d:	88 57 11 	movb	%dl, 17(%rdi)
     850:	88 4f 10 	movb	%cl, 16(%rdi)
     853:	88 57 12 	movb	%dl, 18(%rdi)
     856:	88 57 13 	movb	%dl, 19(%rdi)
     859:	c3 	retq
     85a:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:696
; return
     860:	88 0f 	movb	%cl, (%rdi)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:697
; (
     862:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
     869:	88 57 11 	movb	%dl, 17(%rdi)
     86c:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     870:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     877:	88 57 12 	movb	%dl, 18(%rdi)
     87a:	88 4f 10 	movb	%cl, 16(%rdi)
     87d:	88 57 13 	movb	%dl, 19(%rdi)
     880:	c3 	retq
     881:	0f 1f 80 00 00 00 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:710
; return
     888:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:711
; (
     88f:	40 88 37 	movb	%sil, (%rdi)
     892:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     896:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     89d:	88 57 11 	movb	%dl, 17(%rdi)
     8a0:	88 4f 10 	movb	%cl, 16(%rdi)
     8a3:	88 57 12 	movb	%dl, 18(%rdi)
     8a6:	88 57 13 	movb	%dl, 19(%rdi)
     8a9:	c3 	retq
     8aa:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:724
; return
     8b0:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:725
; (
     8b7:	40 88 37 	movb	%sil, (%rdi)
     8ba:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     8be:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     8c5:	88 57 11 	movb	%dl, 17(%rdi)
     8c8:	88 4f 10 	movb	%cl, 16(%rdi)
     8cb:	88 57 12 	movb	%dl, 18(%rdi)
     8ce:	88 57 13 	movb	%dl, 19(%rdi)
     8d1:	c3 	retq
     8d2:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     8dc:	0f 1f 40 00 	nopl	(%rax)

_error_struct_fixed_header:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:768
; {
     8e0:	41 89 f1 	movl	%esi, %r9d
     8e3:	49 89 d0 	movq	%rdx, %r8
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:770
; (
     8e6:	8b 35 00 00 00 00 	movl	(%rip), %esi
     8ec:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     8f3:	48 8d 0d 00 00 00 00 	leaq	(%rip), %rcx
     8fa:	88 17 	movb	%dl, (%rdi)
     8fc:	48 89 4f 08 	movq	%rcx, 8(%rdi)
     900:	88 57 10 	movb	%dl, 16(%rdi)
     903:	88 57 11 	movb	%dl, 17(%rdi)
     906:	88 57 12 	movb	%dl, 18(%rdi)
     909:	88 57 13 	movb	%dl, 19(%rdi)
     90c:	89 77 14 	movl	%esi, 20(%rdi)
     90f:	89 77 18 	movl	%esi, 24(%rdi)
     912:	48 89 4f 20 	movq	%rcx, 32(%rdi)
     916:	89 77 28 	movl	%esi, 40(%rdi)
     919:	48 89 4f 30 	movq	%rcx, 48(%rdi)
     91d:	4c 89 4f 38 	movq	%r9, 56(%rdi)
     921:	4c 89 47 40 	movq	%r8, 64(%rdi)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:768
; {
     925:	48 89 f8 	movq	%rdi, %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:785
; }
     928:	c3 	retq
     929:	0f 1f 80 00 00 00 00 	nopl	(%rax)

_get_dup_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:788
; {
     930:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
     932:	c1 e8 03 	shrl	$3, %eax
     935:	83 e0 01 	andl	$1, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:794
; }
     938:	c3 	retq
     939:	0f 1f 80 00 00 00 00 	nopl	(%rax)

_get_qos_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:797
; {
     940:	83 e7 06 	andl	$6, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
     943:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     94a:	89 f8 	movl	%edi, %eax
     94c:	d1 f8 	sarl	%eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:799
; if (qos_flag_bits > (uint8_t)2U)
     94e:	83 ff 06 	cmpl	$6, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
     951:	0f 44 c2 	cmovel	%edx, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:803
; }
     954:	c3 	retq
     955:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     95f:	90 	nop

_get_retain_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:806
; {
     960:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
     962:	83 e0 01 	andl	$1, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:812
; }
     965:	c3 	retq
     966:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)

_get_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:815
; {
     970:	89 f0 	movl	%esi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
     972:	83 e0 0f 	andl	$15, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:817
; if
     975:	40 38 3d 00 00 00 00 	cmpb	%dil, (%rip)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:818
; (
     97c:	74 1a 	je	26 <_get_flag+0x28>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:821
; || message_type == define_mqtt_control_packet_SUBSCRIBE
     97e:	40 38 3d 00 00 00 00 	cmpb	%dil, (%rip)
     985:	74 11 	je	17 <_get_flag+0x28>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:822
; || message_type == define_mqtt_control_packet_UNSUBSCRIBE
     987:	40 38 3d 00 00 00 00 	cmpb	%dil, (%rip)
     98e:	74 08 	je	8 <_get_flag+0x28>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:828
; else if (v1 != (uint8_t)0b0000U)
     990:	84 c0 	testb	%al, %al
     992:	75 08 	jne	8 <_get_flag+0x2c>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:832
; }
     994:	c3 	retq
     995:	0f 1f 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:824
; if (v1 != (uint8_t)0b0010U)
     998:	3c 02 	cmpb	$2, %al
     99a:	74 f8 	je	-8 <_get_flag+0x24>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:825
; return max_u8;
     99c:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     9a3:	c3 	retq
     9a4:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     9ae:	66 90 	nop

_get_fixed_header:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:835
; {
     9b0:	41 57 	pushq	%r15
     9b2:	41 56 	pushq	%r14
     9b4:	41 55 	pushq	%r13
     9b6:	41 54 	pushq	%r12
     9b8:	55 	pushq	%rbp
     9b9:	53 	pushq	%rbx
     9ba:	48 83 8c 24 c8 ef ff ff 00 	orq	$0, -4152(%rsp)
     9c3:	48 83 ec 38 	subq	$56, %rsp
     9c7:	44 0f b6 5c 24 73 	movzbl	115(%rsp), %r11d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:836
; if (s._message_type == define_mqtt_control_packet_PUBLISH)
     9cd:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     9d4:	44 0f b6 4c 24 70 	movzbl	112(%rsp), %r9d
     9da:	44 8b 64 24 74 	movl	116(%rsp), %r12d
     9df:	0f b6 6c 24 71 	movzbl	113(%rsp), %ebp
     9e4:	44 0f b6 15 00 00 00 00 	movzbl	(%rip), %r10d
     9ec:	8b 1d 00 00 00 00 	movl	(%rip), %ebx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:835
; {
     9f2:	49 89 f8 	movq	%rdi, %r8
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:836
; if (s._message_type == define_mqtt_control_packet_PUBLISH)
     9f5:	44 38 d9 	cmpb	%r11b, %cl
     9f8:	0f 84 da 00 00 00 	je	218 <_get_fixed_header+0x128>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:957
; uint8_t flag = get_flag(s._message_type, s._fixed_header_first_one_byte);
     9fe:	41 83 e1 0f 	andl	$15, %r9d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:818
; (
     a02:	44 3a 1d 00 00 00 00 	cmpb	(%rip), %r11b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:957
; uint8_t flag = get_flag(s._message_type, s._fixed_header_first_one_byte);
     a09:	41 0f b6 f3 	movzbl	%r11b, %esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:816
; uint8_t v1 = slice_byte(fixed_header_first_one_byte, (uint8_t)4U, (uint8_t)8U);
     a0d:	74 51 	je	81 <_get_fixed_header+0xb0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:821
; || message_type == define_mqtt_control_packet_SUBSCRIBE
     a0f:	44 3a 1d 00 00 00 00 	cmpb	(%rip), %r11b
     a16:	74 48 	je	72 <_get_fixed_header+0xb0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:822
; || message_type == define_mqtt_control_packet_UNSUBSCRIBE
     a18:	44 3a 1d 00 00 00 00 	cmpb	(%rip), %r11b
     a1f:	74 3f 	je	63 <_get_fixed_header+0xb0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:828
; else if (v1 != (uint8_t)0b0000U)
     a21:	45 84 c9 	testb	%r9b, %r9b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:959
; data = get_struct_fixed_header_constant_except_publish(s._message_type);
     a24:	48 8d 7c 24 10 	leaq	16(%rsp), %rdi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:828
; else if (v1 != (uint8_t)0b0000U)
     a29:	45 0f 45 ca 	cmovnel	%r10d, %r9d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:958
; struct_fixed_header_constant
     a2d:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0x82>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:960
; bool
     a32:	40 84 ed 	testb	%bpl, %bpl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:964
; || is_valid_flag(data, flag) == false;
     a35:	75 40 	jne	64 <_get_fixed_header+0xc7>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:545
; return s.flags_constant.flag == flag;
     a37:	44 38 4c 24 20 	cmpb	%r9b, 32(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:964
; || is_valid_flag(data, flag) == false;
     a3c:	0f 85 f6 01 00 00 	jne	502 <_get_fixed_header+0x288>
     a42:	45 38 d3 	cmpb	%r10b, %r11b
     a45:	0f 85 3d 01 00 00 	jne	317 <_get_fixed_header+0x1d8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:977
; error_struct =
     a4b:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     a52:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
     a59:	eb 2a 	jmp	42 <_get_fixed_header+0xd5>
     a5b:	0f 1f 44 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:824
; if (v1 != (uint8_t)0b0010U)
     a60:	41 80 f9 02 	cmpb	$2, %r9b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:959
; data = get_struct_fixed_header_constant_except_publish(s._message_type);
     a64:	48 8d 7c 24 10 	leaq	16(%rsp), %rdi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:824
; if (v1 != (uint8_t)0b0010U)
     a69:	45 0f 45 ca 	cmovnel	%r10d, %r9d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:958
; struct_fixed_header_constant
     a6d:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0xc2>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:960
; bool
     a72:	40 84 ed 	testb	%bpl, %bpl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:964
; || is_valid_flag(data, flag) == false;
     a75:	74 c0 	je	-64 <_get_fixed_header+0x87>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:965
; if (have_error)
     a77:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:969
; error_struct =
     a7e:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:992
; return error_struct_fixed_header(error_struct);
     a85:	48 8d 05 00 00 00 00 	leaq	(%rip), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:770
; (
     a8c:	45 88 10 	movb	%r10b, (%r8)
     a8f:	49 89 40 08 	movq	%rax, 8(%r8)
     a93:	45 88 50 10 	movb	%r10b, 16(%r8)
     a97:	45 88 50 11 	movb	%r10b, 17(%r8)
     a9b:	45 88 50 12 	movb	%r10b, 18(%r8)
     a9f:	45 88 50 13 	movb	%r10b, 19(%r8)
     aa3:	41 89 58 14 	movl	%ebx, 20(%r8)
     aa7:	41 89 58 18 	movl	%ebx, 24(%r8)
     aab:	49 89 40 20 	movq	%rax, 32(%r8)
     aaf:	41 89 58 28 	movl	%ebx, 40(%r8)
     ab3:	49 89 40 30 	movq	%rax, 48(%r8)
     ab7:	41 88 48 38 	movb	%cl, 56(%r8)
     abb:	49 89 50 40 	movq	%rdx, 64(%r8)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1017
; }
     abf:	48 83 c4 38 	addq	$56, %rsp
     ac3:	5b 	popq	%rbx
     ac4:	5d 	popq	%rbp
     ac5:	41 5c 	popq	%r12
     ac7:	41 5d 	popq	%r13
     ac9:	41 5e 	popq	%r14
     acb:	4c 89 c0 	movq	%r8, %rax
     ace:	41 5f 	popq	%r15
     ad0:	c3 	retq
     ad1:	0f 1f 80 00 00 00 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
     ad8:	44 89 c8 	movl	%r9d, %eax
     adb:	c1 e8 03 	shrl	$3, %eax
     ade:	83 e0 01 	andl	$1, %eax
     ae1:	89 c2 	movl	%eax, %edx
     ae3:	44 89 c8 	movl	%r9d, %eax
     ae6:	83 e0 06 	andl	$6, %eax
     ae9:	41 89 c5 	movl	%eax, %r13d
     aec:	44 0f b6 5c 24 72 	movzbl	114(%rsp), %r11d
     af2:	8b 74 24 78 	movl	120(%rsp), %esi
     af6:	0f b6 bc 24 88 00 00 00 	movzbl	136(%rsp), %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:838
; uint8_t dup_flag = get_dup_flag(s._fixed_header_first_one_byte);
     afe:	41 d1 fd 	sarl	%r13d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:799
; if (qos_flag_bits > (uint8_t)2U)
     b01:	41 83 e1 01 	andl	$1, %r9d
     b05:	83 f8 06 	cmpl	$6, %eax
     b08:	0f 84 d2 00 00 00 	je	210 <_get_fixed_header+0x230>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:840
; uint8_t retain_flag = get_retain_flag(s._fixed_header_first_one_byte);
     b0e:	40 84 ed 	testb	%bpl, %bpl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:851
; || s._payload_error_status > (uint8_t)0U;
     b11:	0f 85 60 ff ff ff 	jne	-160 <_get_fixed_header+0xc7>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:844
; || s._message_type == max_u8
     b17:	44 38 d1 	cmpb	%r10b, %cl
     b1a:	41 0f 94 c6 	sete	%r14b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:845
; || dup_flag == max_u8
     b1e:	44 38 d2 	cmpb	%r10b, %dl
     b21:	0f 94 c0 	sete	%al
     b24:	44 09 f0 	orl	%r14d, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:846
; || qos_flag == max_u8
     b27:	45 38 d5 	cmpb	%r10b, %r13b
     b2a:	40 0f 94 c5 	sete	%bpl
     b2e:	09 c5 	orl	%eax, %ebp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:847
; || retain_flag == max_u8
     b30:	45 38 d1 	cmpb	%r10b, %r9b
     b33:	41 0f 94 c7 	sete	%r15b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:848
; || s._topic_name_error_status > (uint8_t)0U
     b37:	40 84 ff 	testb	%dil, %dil
     b3a:	40 88 6c 24 0f 	movb	%bpl, 15(%rsp)
     b3f:	40 0f 95 c7 	setne	%dil
     b43:	44 89 fd 	movl	%r15d, %ebp
     b46:	40 08 fd 	orb	%dil, %bpl
     b49:	75 0b 	jne	11 <_get_fixed_header+0x1a6>
     b4b:	80 7c 24 0f 00 	cmpb	$0, 15(%rsp)
     b50:	0f 84 c2 00 00 00 	je	194 <_get_fixed_header+0x268>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:852
; if (have_error)
     b56:	45 84 f6 	testb	%r14b, %r14b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:863
; else if (s._message_type == max_u8)
     b59:	0f 85 ec fe ff ff 	jne	-276 <_get_fixed_header+0x9b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:871
; else if (dup_flag == max_u8)
     b5f:	84 c0 	testb	%al, %al
     b61:	0f 85 f1 00 00 00 	jne	241 <_get_fixed_header+0x2a8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:879
; else if (qos_flag == max_u8)
     b67:	80 7c 24 0f 00 	cmpb	$0, 15(%rsp)
     b6c:	0f 84 fe 00 00 00 	je	254 <_get_fixed_header+0x2c0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:880
; error_struct =
     b72:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     b79:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
     b80:	e9 00 ff ff ff 	jmp	-256 <_get_fixed_header+0xd5>
     b85:	0f 1f 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:965
; if (have_error)
     b88:	0f b6 44 24 10 	movzbl	16(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:996
; (
     b8d:	45 89 60 14 	movl	%r12d, 20(%r8)
     b91:	41 88 00 	movb	%al, (%r8)
     b94:	48 8b 44 24 18 	movq	24(%rsp), %rax
     b99:	41 89 58 18 	movl	%ebx, 24(%r8)
     b9d:	49 89 40 08 	movq	%rax, 8(%r8)
     ba1:	8b 44 24 20 	movl	32(%rsp), %eax
     ba5:	41 89 58 28 	movl	%ebx, 40(%r8)
     ba9:	41 89 40 10 	movl	%eax, 16(%r8)
     bad:	48 8d 05 00 00 00 00 	leaq	(%rip), %rax
     bb4:	49 89 40 20 	movq	%rax, 32(%r8)
     bb8:	49 89 40 30 	movq	%rax, 48(%r8)
     bbc:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     bc3:	41 88 40 38 	movb	%al, 56(%r8)
     bc7:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
     bce:	49 89 40 40 	movq	%rax, 64(%r8)
     bd2:	e9 e8 fe ff ff 	jmp	-280 <_get_fixed_header+0x10f>
     bd7:	66 0f 1f 84 00 00 00 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:800
; return max_u8;
     be0:	40 84 ed 	testb	%bpl, %bpl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:851
; || s._payload_error_status > (uint8_t)0U;
     be3:	0f 85 8e fe ff ff 	jne	-370 <_get_fixed_header+0xc7>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:844
; || s._message_type == max_u8
     be9:	44 38 d1 	cmpb	%r10b, %cl
     bec:	41 0f 94 c6 	sete	%r14b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:845
; || dup_flag == max_u8
     bf0:	44 38 d2 	cmpb	%r10b, %dl
     bf3:	0f 94 c0 	sete	%al
     bf6:	44 09 f0 	orl	%r14d, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:847
; || retain_flag == max_u8
     bf9:	45 38 d1 	cmpb	%r10b, %r9b
     bfc:	41 0f 94 c7 	sete	%r15b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:848
; || s._topic_name_error_status > (uint8_t)0U
     c00:	40 84 ff 	testb	%dil, %dil
     c03:	c6 44 24 0f 01 	movb	$1, 15(%rsp)
     c08:	40 0f 95 c7 	setne	%dil
     c0c:	e9 45 ff ff ff 	jmp	-187 <_get_fixed_header+0x1a6>
     c11:	0f 1f 80 00 00 00 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:849
; || s._topic_length == max_u32
     c18:	39 de 	cmpl	%ebx, %esi
     c1a:	74 70 	je	112 <_get_fixed_header+0x2dc>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:850
; || s.is_searching_property_length
     c1c:	45 84 db 	testb	%r11b, %r11b
     c1f:	74 7e 	je	126 <_get_fixed_header+0x2ef>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:912
; error_struct =
     c21:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     c28:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
     c2f:	e9 51 fe ff ff 	jmp	-431 <_get_fixed_header+0xd5>
     c34:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:965
; if (have_error)
     c38:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:985
; error_struct =
     c3f:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:976
; else if (s._message_type == max_u8)
     c46:	45 38 d3 	cmpb	%r10b, %r11b
     c49:	0f 85 36 fe ff ff 	jne	-458 <_get_fixed_header+0xd5>
     c4f:	e9 f7 fd ff ff 	jmp	-521 <_get_fixed_header+0x9b>
     c54:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:872
; error_struct =
     c58:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     c5f:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
     c66:	e9 1a fe ff ff 	jmp	-486 <_get_fixed_header+0xd5>
     c6b:	0f 1f 44 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:887
; else if (retain_flag == max_u8)
     c70:	45 84 ff 	testb	%r15b, %r15b
     c73:	0f 84 8e 00 00 00 	je	142 <_get_fixed_header+0x357>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:888
; error_struct =
     c79:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     c80:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
     c87:	e9 f9 fd ff ff 	jmp	-519 <_get_fixed_header+0xd5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:896
; error_struct =
     c8c:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     c93:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
     c9a:	e9 e6 fd ff ff 	jmp	-538 <_get_fixed_header+0xd5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:851
; || s._payload_error_status > (uint8_t)0U;
     c9f:	80 bc 24 98 00 00 00 00 	cmpb	$0, 152(%rsp)
     ca7:	74 17 	je	23 <_get_fixed_header+0x310>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:920
; error_struct =
     ca9:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     cb0:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:927
; return error_struct_fixed_header(error_struct);
     cb7:	e9 c9 fd ff ff 	jmp	-567 <_get_fixed_header+0xd5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:769
; return
     cbc:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:852
; if (have_error)
     cc0:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:933
; (
     cc7:	41 88 08 	movb	%cl, (%r8)
     cca:	49 89 40 08 	movq	%rax, 8(%r8)
     cce:	48 8b 84 24 80 00 00 00 	movq	128(%rsp), %rax
     cd6:	45 88 50 10 	movb	%r10b, 16(%r8)
     cda:	49 89 40 20 	movq	%rax, 32(%r8)
     cde:	41 88 50 11 	movb	%dl, 17(%r8)
     ce2:	45 88 68 12 	movb	%r13b, 18(%r8)
     ce6:	45 88 48 13 	movb	%r9b, 19(%r8)
     cea:	45 89 60 14 	movl	%r12d, 20(%r8)
     cee:	41 89 70 18 	movl	%esi, 24(%r8)
     cf2:	41 c7 40 28 00 00 00 00 	movl	$0, 40(%r8)
     cfa:	48 8b 84 24 90 00 00 00 	movq	144(%rsp), %rax
     d02:	e9 b1 fe ff ff 	jmp	-335 <_get_fixed_header+0x208>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:895
; else if (s._topic_length == max_u32)
     d07:	39 de 	cmpl	%ebx, %esi
     d09:	0f 84 7d ff ff ff 	je	-131 <_get_fixed_header+0x2dc>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:903
; else if (s._topic_name_error_status > (uint8_t)0U)
     d0f:	40 84 ff 	testb	%dil, %dil
     d12:	74 13 	je	19 <_get_fixed_header+0x377>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:904
; error_struct =
     d14:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     d1b:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
     d22:	e9 5e fd ff ff 	jmp	-674 <_get_fixed_header+0xd5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:911
; else if (s.is_searching_property_length)
     d27:	45 84 db 	testb	%r11b, %r11b
     d2a:	0f 84 79 ff ff ff 	je	-135 <_get_fixed_header+0x2f9>
     d30:	e9 ec fe ff ff 	jmp	-276 <_get_fixed_header+0x271>
     d35:	66 2e 0f 1f 84 00 00 00 00 00 	nopw	%cs:(%rax,%rax)
     d3f:	90 	nop

_mqtt_packet_parse:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1020
; {
     d40:	41 57 	pushq	%r15
     d42:	49 c7 c3 00 f0 ff ff 	movq	$-4096, %r11
     d49:	41 56 	pushq	%r14
     d4b:	41 55 	pushq	%r13
     d4d:	41 54 	pushq	%r12
     d4f:	55 	pushq	%rbp
     d50:	53 	pushq	%rbx
     d51:	49 81 eb 00 10 00 00 	subq	$4096, %r11
     d58:	4a 83 0c 1c 00 	orq	$0, (%rsp,%r11)
     d5d:	49 81 fb 00 f0 fe ff 	cmpq	$-69632, %r11
     d64:	75 eb 	jne	-21 <_mqtt_packet_parse+0x11>
     d66:	4a 83 8c 1c 78 ff ff ff 00 	orq	$0, -136(%rsp,%r11)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1021
; bool ptr_is_break = false;
     d6f:	c5 f9 ef c0 	vpxor	%xmm0, %xmm0, %xmm0
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1020
; {
     d73:	48 81 ec 88 00 01 00 	subq	$65672, %rsp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1029
; uint32_t ptr_topic_length = max_u32;
     d7a:	8b 0d 00 00 00 00 	movl	(%rip), %ecx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1020
; {
     d80:	89 54 24 48 	movl	%edx, 72(%rsp)
     d84:	89 d3 	movl	%edx, %ebx
     d86:	49 89 fc 	movq	%rdi, %r12
     d89:	48 89 f5 	movq	%rsi, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1030
; uint8_t ptr_topic_name_u8[65536U] = { 0U };
     d8c:	48 8d bc 24 90 00 00 00 	leaq	144(%rsp), %rdi
     d94:	31 f6 	xorl	%esi, %esi
     d96:	ba f0 ff 00 00 	movl	$65520, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1029
; uint32_t ptr_topic_length = max_u32;
     d9b:	89 4c 24 04 	movl	%ecx, 4(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1025
; uint8_t ptr_for_decoding_packets[4U] = { 0U };
     d9f:	c7 44 24 5c 00 00 00 00 	movl	$0, 92(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1023
; uint8_t ptr_message_type = max_u8;
     da7:	44 0f b6 3d 00 00 00 00 	movzbl	(%rip), %r15d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1024
; bool ptris_searching_remaining_length = true;
     daf:	c5 f8 29 84 24 80 00 00 00 	vmovaps	%xmm0, 128(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1030
; uint8_t ptr_topic_name_u8[65536U] = { 0U };
     db8:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x7d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1031
; C_String_t ptr_topic_name = "";
     dbd:	85 db 	testl	%ebx, %ebx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1037
; for (uint32_t i = (uint32_t)0U; i < packet_size; i = i + (uint32_t)1U)
     dbf:	44 0f b6 15 00 00 00 00 	movzbl	(%rip), %r10d
     dc7:	8b 4c 24 04 	movl	4(%rsp), %ecx
     dcb:	0f 84 6f 04 00 00 	je	1135 <_mqtt_packet_parse+0x500>
     dd1:	44 8d 43 ff 	leal	-1(%rbx), %r8d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1035
; C_String_t ptr_payload = "";
     dd5:	4c 8d 0d 00 00 00 00 	leaq	(%rip), %r9
     ddc:	44 89 44 24 24 	movl	%r8d, 36(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1029
; uint32_t ptr_topic_length = max_u32;
     de1:	89 4c 24 14 	movl	%ecx, 20(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1036
; uint8_t ptr_payload_error_status = (uint8_t)0U;
     de5:	c6 44 24 4d 00 	movb	$0, 77(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1034
; bool ptris_searching_property_length = true;
     dea:	c6 44 24 4c 01 	movb	$1, 76(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1032
; uint8_t ptr_topic_name_error_status = (uint8_t)0U;
     def:	c6 44 24 23 00 	movb	$0, 35(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1031
; C_String_t ptr_topic_name = "";
     df4:	4c 89 4c 24 08 	movq	%r9, 8(%rsp)
     df9:	4c 89 4c 24 18 	movq	%r9, 24(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1028
; uint8_t ptr_for_topic_length = (uint8_t)0U;
     dfe:	c6 44 24 4e 00 	movb	$0, 78(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1027
; uint32_t ptr_variable_header_index = (uint32_t)0U;
     e03:	c7 44 24 04 00 00 00 00 	movl	$0, 4(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1026
; uint32_t ptr_remaining_length = (uint32_t)0U;
     e0b:	c7 44 24 10 00 00 00 00 	movl	$0, 16(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1037
; for (uint32_t i = (uint32_t)0U; i < packet_size; i = i + (uint32_t)1U)
     e13:	31 db 	xorl	%ebx, %ebx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1024
; bool ptris_searching_remaining_length = true;
     e15:	ba 01 00 00 00 	movl	$1, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1022
; uint8_t ptr_fixed_header_first_one_byte = (uint8_t)0U;
     e1a:	45 31 f6 	xorl	%r14d, %r14d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1021
; bool ptr_is_break = false;
     e1d:	45 31 db 	xorl	%r11d, %r11d
     e20:	eb 2a 	jmp	42 <_mqtt_packet_parse+0x10c>
     e22:	66 0f 1f 44 00 00 	nopw	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1055
; else if (i >= (uint32_t)1U && i <= (uint32_t)4U && is_searching_remaining_length)
     e28:	8d 73 ff 	leal	-1(%rbx), %esi
     e2b:	83 fe 03 	cmpl	$3, %esi
     e2e:	0f 86 d4 00 00 00 	jbe	212 <_mqtt_packet_parse+0x1c8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1067
; else if (!is_searching_remaining_length)
     e34:	84 d2 	testb	%dl, %dl
     e36:	0f 84 d4 00 00 00 	je	212 <_mqtt_packet_parse+0x1d0>
     e3c:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1037
; for (uint32_t i = (uint32_t)0U; i < packet_size; i = i + (uint32_t)1U)
     e40:	48 8d 43 01 	leaq	1(%rbx), %rax
     e44:	49 39 d8 	cmpq	%rbx, %r8
     e47:	74 57 	je	87 <_mqtt_packet_parse+0x160>
     e49:	48 89 c3 	movq	%rax, %rbx
     e4c:	41 89 dd 	movl	%ebx, %r13d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1039
; uint8_t one_byte = request[i];
     e4f:	45 84 db 	testb	%r11b, %r11b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1042
; if (!is_break)
     e52:	75 ec 	jne	-20 <_mqtt_packet_parse+0x100>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1039
; uint8_t one_byte = request[i];
     e54:	0f b6 7c 1d 00 	movzbl	(%rbp,%rbx), %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1043
; if (i == (uint32_t)0U)
     e59:	48 8d 44 1d 00 	leaq	(%rbp,%rbx), %rax
     e5e:	48 85 db 	testq	%rbx, %rbx
     e61:	75 c5 	jne	-59 <_mqtt_packet_parse+0xe8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1045
; uint8_t message_type_bits = slice_byte(one_byte, (uint8_t)0U, (uint8_t)4U);
     e63:	89 f8 	movl	%edi, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
     e65:	25 f0 00 00 00 	andl	$240, %eax
     e6a:	c1 f8 04 	sarl	$4, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:340
; if (message_type_bits < (uint8_t)1U || message_type_bits > (uint8_t)15U)
     e6d:	44 8d 68 ff 	leal	-1(%rax), %r13d
     e71:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
     e78:	41 89 c7 	movl	%eax, %r15d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1046
; uint8_t message_type = get_message_type(message_type_bits);
     e7b:	41 80 fd 0e 	cmpb	$14, %r13b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:340
; if (message_type_bits < (uint8_t)1U || message_type_bits > (uint8_t)15U)
     e7f:	76 6f 	jbe	111 <_mqtt_packet_parse+0x1b0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1052
; ptris_searching_remaining_length = false;
     e81:	31 d2 	xorl	%edx, %edx
     e83:	41 89 f7 	movl	%esi, %r15d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1039
; uint8_t one_byte = request[i];
     e86:	41 89 fe 	movl	%edi, %r14d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1051
; ptr_is_break = true;
     e89:	41 bb 01 00 00 00 	movl	$1, %r11d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1037
; for (uint32_t i = (uint32_t)0U; i < packet_size; i = i + (uint32_t)1U)
     e8f:	48 8d 43 01 	leaq	1(%rbx), %rax
     e93:	49 39 d8 	cmpq	%rbx, %r8
     e96:	75 b1 	jne	-79 <_mqtt_packet_parse+0x109>
     e98:	0f 1f 84 00 00 00 00 00 	nopl	(%rax,%rax)
     ea0:	44 0f b6 05 00 00 00 00 	movzbl	(%rip), %r8d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1156
; bool is_searching_remaining_length = ptris_searching_remaining_length;
     ea8:	45 38 fa 	cmpb	%r15b, %r10b
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:836
; if (s._message_type == define_mqtt_control_packet_PUBLISH)
     eab:	0f 84 07 02 00 00 	je	519 <_mqtt_packet_parse+0x378>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:957
; uint8_t flag = get_flag(s._message_type, s._fixed_header_first_one_byte);
     eb1:	41 83 e6 0f 	andl	$15, %r14d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:818
; (
     eb5:	44 38 3d 00 00 00 00 	cmpb	%r15b, (%rip)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:957
; uint8_t flag = get_flag(s._message_type, s._fixed_header_first_one_byte);
     ebc:	41 0f b6 f7 	movzbl	%r15b, %esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:816
; uint8_t v1 = slice_byte(fixed_header_first_one_byte, (uint8_t)4U, (uint8_t)8U);
     ec0:	0f 84 e2 00 00 00 	je	226 <_mqtt_packet_parse+0x268>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:821
; || message_type == define_mqtt_control_packet_SUBSCRIBE
     ec6:	44 38 3d 00 00 00 00 	cmpb	%r15b, (%rip)
     ecd:	0f 84 d5 00 00 00 	je	213 <_mqtt_packet_parse+0x268>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:822
; || message_type == define_mqtt_control_packet_UNSUBSCRIBE
     ed3:	44 38 3d 00 00 00 00 	cmpb	%r15b, (%rip)
     eda:	0f 84 c8 00 00 00 	je	200 <_mqtt_packet_parse+0x268>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:828
; else if (v1 != (uint8_t)0b0000U)
     ee0:	45 84 f6 	testb	%r14b, %r14b
     ee3:	45 0f 45 f0 	cmovnel	%r8d, %r14d
     ee7:	e9 c4 00 00 00 	jmp	196 <_mqtt_packet_parse+0x270>
     eec:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1047
; ptr_message_type = message_type;
     ef0:	40 38 c6 	cmpb	%al, %sil
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1052
; ptris_searching_remaining_length = false;
     ef3:	41 0f 44 d3 	cmovel	%r11d, %edx
     ef7:	41 89 fe 	movl	%edi, %r14d
     efa:	41 0f 94 c3 	sete	%r11b
     efe:	e9 3d ff ff ff 	jmp	-195 <_mqtt_packet_parse+0x100>
     f03:	0f 1f 44 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1055
; else if (i >= (uint32_t)1U && i <= (uint32_t)4U && is_searching_remaining_length)
     f08:	84 d2 	testb	%dl, %dl
     f0a:	88 54 24 28 	movb	%dl, 40(%rsp)
     f0e:	75 30 	jne	48 <_mqtt_packet_parse+0x200>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1069
; uint32_t variable_header_index = ptr_variable_header_index;
     f10:	31 f6 	xorl	%esi, %esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1072
; if (message_type == define_mqtt_control_packet_PUBLISH)
     f12:	45 38 fa 	cmpb	%r15b, %r10b
     f15:	0f 84 25 01 00 00 	je	293 <_mqtt_packet_parse+0x300>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1152
; if (variable_header_index <= max_u32 - (uint32_t)1U)
     f1b:	8d 41 ff 	leal	-1(%rcx), %eax
     f1e:	31 d2 	xorl	%edx, %edx
     f20:	41 89 f3 	movl	%esi, %r11d
     f23:	3b 44 24 04 	cmpl	4(%rsp), %eax
     f27:	0f 82 13 ff ff ff 	jb	-237 <_mqtt_packet_parse+0x100>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1153
; ptr_variable_header_index = variable_header_index + (uint32_t)1U;
     f2d:	ff 44 24 04 	incl	4(%rsp)
     f31:	31 d2 	xorl	%edx, %edx
     f33:	41 89 f3 	movl	%esi, %r11d
     f36:	e9 05 ff ff ff 	jmp	-251 <_mqtt_packet_parse+0x100>
     f3b:	0f 1f 44 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1059
; ptr_for_decoding_packets[i_minus_one] = one_byte;
     f40:	40 88 7c 34 5c 	movb	%dil, 92(%rsp,%rsi)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:328
; uint32_t untrust_r = decodeing_variable_bytes(ptr_for_decoding_packets, bytes_length);
     f45:	48 8d 7c 24 5c 	leaq	92(%rsp), %rdi
     f4a:	89 de 	movl	%ebx, %esi
     f4c:	44 88 54 24 4f 	movb	%r10b, 79(%rsp)
     f51:	4c 89 44 24 40 	movq	%r8, 64(%rsp)
     f56:	4c 89 4c 24 38 	movq	%r9, 56(%rsp)
     f5b:	89 4c 24 30 	movl	%ecx, 48(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1057
; uint8_t i_u8 = (uint8_t)i;
     f5f:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x224>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:329
; if (untrust_r != max_u32)
     f64:	8b 4c 24 30 	movl	48(%rsp), %ecx
     f68:	4c 8b 4c 24 38 	movq	56(%rsp), %r9
     f6d:	39 c8 	cmpl	%ecx, %eax
     f6f:	4c 8b 44 24 40 	movq	64(%rsp), %r8
     f74:	44 0f b6 54 24 4f 	movzbl	79(%rsp), %r10d
     f7a:	0f b6 54 24 28 	movzbl	40(%rsp), %edx
     f7f:	0f 84 bb fe ff ff 	je	-325 <_mqtt_packet_parse+0x100>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:330
; if (bytes_length_u32 + untrust_r == fixed_value)
     f85:	8b 7c 24 24 	movl	36(%rsp), %edi
     f89:	41 01 c5 	addl	%eax, %r13d
     f8c:	41 39 fd 	cmpl	%edi, %r13d
     f8f:	0f 45 44 24 10 	cmovnel	16(%rsp), %eax
     f94:	41 0f 44 d3 	cmovel	%r11d, %edx
     f98:	89 44 24 10 	movl	%eax, 16(%rsp)
     f9c:	e9 9f fe ff ff 	jmp	-353 <_mqtt_packet_parse+0x100>
     fa1:	0f 1f 80 00 00 00 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:824
; if (v1 != (uint8_t)0b0010U)
     fa8:	41 80 fe 02 	cmpb	$2, %r14b
     fac:	45 0f 45 f0 	cmovnel	%r8d, %r14d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:959
; data = get_struct_fixed_header_constant_except_publish(s._message_type);
     fb0:	48 8d 7c 24 60 	leaq	96(%rsp), %rdi
     fb5:	89 4c 24 14 	movl	%ecx, 20(%rsp)
     fb9:	88 54 24 04 	movb	%dl, 4(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:958
; struct_fixed_header_constant
     fbd:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x282>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:960
; bool
     fc2:	0f b6 54 24 04 	movzbl	4(%rsp), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:964
; || is_valid_flag(data, flag) == false;
     fc7:	8b 4c 24 14 	movl	20(%rsp), %ecx
     fcb:	84 d2 	testb	%dl, %dl
     fcd:	0f 84 6d 01 00 00 	je	365 <_mqtt_packet_parse+0x400>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:965
; if (have_error)
     fd3:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:969
; error_struct =
     fda:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:992
; return error_struct_fixed_header(error_struct);
     fe1:	48 8b 74 24 08 	movq	8(%rsp), %rsi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:770
; (
     fe6:	45 88 04 24 	movb	%r8b, (%r12)
     fea:	49 89 74 24 08 	movq	%rsi, 8(%r12)
     fef:	45 88 44 24 10 	movb	%r8b, 16(%r12)
     ff4:	45 88 44 24 11 	movb	%r8b, 17(%r12)
     ff9:	45 88 44 24 12 	movb	%r8b, 18(%r12)
     ffe:	45 88 44 24 13 	movb	%r8b, 19(%r12)
    1003:	41 89 4c 24 14 	movl	%ecx, 20(%r12)
    1008:	41 89 4c 24 18 	movl	%ecx, 24(%r12)
    100d:	49 89 74 24 20 	movq	%rsi, 32(%r12)
    1012:	41 89 4c 24 28 	movl	%ecx, 40(%r12)
    1017:	49 89 74 24 30 	movq	%rsi, 48(%r12)
    101c:	41 88 54 24 38 	movb	%dl, 56(%r12)
    1021:	49 89 44 24 40 	movq	%rax, 64(%r12)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1179
; }
    1026:	48 81 c4 88 00 01 00 	addq	$65672, %rsp
    102d:	5b 	popq	%rbx
    102e:	5d 	popq	%rbp
    102f:	4c 89 e0 	movq	%r12, %rax
    1032:	41 5c 	popq	%r12
    1034:	41 5d 	popq	%r13
    1036:	41 5e 	popq	%r14
    1038:	41 5f 	popq	%r15
    103a:	c3 	retq
    103b:	0f 1f 44 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1073
; if (variable_header_index == (uint32_t)0U)
    1040:	8b 54 24 04 	movl	4(%rsp), %edx
    1044:	85 d2 	testl	%edx, %edx
    1046:	0f 84 dc 01 00 00 	je	476 <_mqtt_packet_parse+0x4e8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1075
; else if (variable_header_index == (uint32_t)1U)
    104c:	83 fa 01 	cmpl	$1, %edx
    104f:	0f 84 06 03 00 00 	je	774 <_mqtt_packet_parse+0x61b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1091
; else if (variable_header_index >= (uint32_t)2U)
    1055:	8b 54 24 14 	movl	20(%rsp), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1097
; ptr_is_break = true;
    1059:	be 01 00 00 00 	movl	$1, %esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1094
; if (topic_length == max_u32)
    105e:	39 ca 	cmpl	%ecx, %edx
    1060:	0f 84 b5 fe ff ff 	je	-331 <_mqtt_packet_parse+0x1db>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1100
; else if (variable_header_index <= topic_length + (uint32_t)1U)
    1066:	44 8b 5c 24 04 	movl	4(%rsp), %r11d
    106b:	ff c2 	incl	%edx
    106d:	44 39 da 	cmpl	%r11d, %edx
    1070:	0f 82 16 03 00 00 	jb	790 <_mqtt_packet_parse+0x64c>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1102
; ptr_topic_name_u8[variable_header_index - (uint32_t)2U] = one_byte;
    1076:	41 8d 43 fe 	leal	-2(%r11), %eax
    107a:	40 88 bc 04 80 00 00 00 	movb	%dil, 128(%rsp,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1103
; if (variable_header_index == topic_length + (uint32_t)1U)
    1082:	be 00 00 00 00 	movl	$0, %esi
    1087:	0f 85 8e fe ff ff 	jne	-370 <_mqtt_packet_parse+0x1db>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1105
; C_String_t topic_name;
    108d:	80 bc 24 7f 00 01 00 00 	cmpb	$0, 65663(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1106
; if (ptr_topic_name_u8[65535U] == (uint8_t)0U)
    1095:	0f 84 8f 03 00 00 	je	911 <_mqtt_packet_parse+0x6ea>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1111
; topic_name = "";
    109b:	48 8d 05 00 00 00 00 	leaq	(%rip), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1110
; ptr_topic_name_error_status = (uint8_t)1U;
    10a2:	c6 44 24 23 01 	movb	$1, 35(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1111
; topic_name = "";
    10a7:	48 89 44 24 18 	movq	%rax, 24(%rsp)
    10ac:	e9 6a fe ff ff 	jmp	-406 <_mqtt_packet_parse+0x1db>
    10b1:	0f 1f 80 00 00 00 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:838
; uint8_t dup_flag = get_dup_flag(s._fixed_header_first_one_byte);
    10b8:	44 89 f7 	movl	%r14d, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
    10bb:	44 89 f0 	movl	%r14d, %eax
    10be:	83 e7 06 	andl	$6, %edi
    10c1:	c1 e8 03 	shrl	$3, %eax
    10c4:	89 fe 	movl	%edi, %esi
    10c6:	83 e0 01 	andl	$1, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:790
; if (dup_flag_bits > (uint8_t)1U)
    10c9:	d1 fe 	sarl	%esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:799
; if (qos_flag_bits > (uint8_t)2U)
    10cb:	41 83 e6 01 	andl	$1, %r14d
    10cf:	83 ff 06 	cmpl	$6, %edi
    10d2:	0f 84 a8 01 00 00 	je	424 <_mqtt_packet_parse+0x540>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:840
; uint8_t retain_flag = get_retain_flag(s._fixed_header_first_one_byte);
    10d8:	84 d2 	testb	%dl, %dl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:851
; || s._payload_error_status > (uint8_t)0U;
    10da:	0f 84 e8 00 00 00 	je	232 <_mqtt_packet_parse+0x488>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:852
; if (have_error)
    10e0:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:856
; error_struct =
    10e7:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:927
; return error_struct_fixed_header(error_struct);
    10ee:	48 8b 7c 24 08 	movq	8(%rsp), %rdi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:770
; (
    10f3:	45 88 04 24 	movb	%r8b, (%r12)
    10f7:	49 89 7c 24 08 	movq	%rdi, 8(%r12)
    10fc:	45 88 44 24 10 	movb	%r8b, 16(%r12)
    1101:	45 88 44 24 11 	movb	%r8b, 17(%r12)
    1106:	45 88 44 24 12 	movb	%r8b, 18(%r12)
    110b:	45 88 44 24 13 	movb	%r8b, 19(%r12)
    1110:	41 89 4c 24 14 	movl	%ecx, 20(%r12)
    1115:	41 89 4c 24 18 	movl	%ecx, 24(%r12)
    111a:	49 89 7c 24 20 	movq	%rdi, 32(%r12)
    111f:	41 89 4c 24 28 	movl	%ecx, 40(%r12)
    1124:	49 89 7c 24 30 	movq	%rdi, 48(%r12)
    1129:	41 88 54 24 38 	movb	%dl, 56(%r12)
    112e:	49 89 44 24 40 	movq	%rax, 64(%r12)
    1133:	e9 ee fe ff ff 	jmp	-274 <_mqtt_packet_parse+0x2e6>
    1138:	0f 1f 84 00 00 00 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:545
; return s.flags_constant.flag == flag;
    1140:	44 38 74 24 70 	cmpb	%r14b, 112(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:964
; || is_valid_flag(data, flag) == false;
    1145:	0f 85 25 02 00 00 	jne	549 <_mqtt_packet_parse+0x630>
    114b:	45 38 f8 	cmpb	%r15b, %r8b
    114e:	75 18 	jne	24 <_mqtt_packet_parse+0x428>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:977
; error_struct =
    1150:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
    1157:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
    115e:	e9 7e fe ff ff 	jmp	-386 <_mqtt_packet_parse+0x2a1>
    1163:	0f 1f 44 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:965
; if (have_error)
    1168:	0f b6 44 24 60 	movzbl	96(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:996
; (
    116d:	41 89 4c 24 18 	movl	%ecx, 24(%r12)
    1172:	41 88 04 24 	movb	%al, (%r12)
    1176:	48 8b 44 24 68 	movq	104(%rsp), %rax
    117b:	41 89 4c 24 28 	movl	%ecx, 40(%r12)
    1180:	49 89 44 24 08 	movq	%rax, 8(%r12)
    1185:	8b 44 24 70 	movl	112(%rsp), %eax
    1189:	41 89 44 24 10 	movl	%eax, 16(%r12)
    118e:	8b 44 24 10 	movl	16(%rsp), %eax
    1192:	41 89 44 24 14 	movl	%eax, 20(%r12)
    1197:	48 8b 44 24 08 	movq	8(%rsp), %rax
    119c:	49 89 44 24 20 	movq	%rax, 32(%r12)
    11a1:	49 89 44 24 30 	movq	%rax, 48(%r12)
    11a6:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    11ad:	41 88 44 24 38 	movb	%al, 56(%r12)
    11b2:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
    11b9:	49 89 44 24 40 	movq	%rax, 64(%r12)
    11be:	e9 63 fe ff ff 	jmp	-413 <_mqtt_packet_parse+0x2e6>
    11c3:	0f 1f 44 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:844
; || s._message_type == max_u8
    11c8:	45 38 d0 	cmpb	%r10b, %r8b
    11cb:	0f 94 c3 	sete	%bl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:845
; || dup_flag == max_u8
    11ce:	44 38 c0 	cmpb	%r8b, %al
    11d1:	0f 94 c2 	sete	%dl
    11d4:	09 da 	orl	%ebx, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:846
; || qos_flag == max_u8
    11d6:	44 38 c6 	cmpb	%r8b, %sil
    11d9:	40 0f 94 c7 	sete	%dil
    11dd:	09 d7 	orl	%edx, %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:847
; || retain_flag == max_u8
    11df:	45 38 c6 	cmpb	%r8b, %r14b
    11e2:	41 0f 94 c3 	sete	%r11b
    11e6:	41 09 fb 	orl	%edi, %r11d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:848
; || s._topic_name_error_status > (uint8_t)0U
    11e9:	80 7c 24 23 00 	cmpb	$0, 35(%rsp)
    11ee:	75 09 	jne	9 <_mqtt_packet_parse+0x4b9>
    11f0:	45 84 db 	testb	%r11b, %r11b
    11f3:	0f 84 c0 00 00 00 	je	192 <_mqtt_packet_parse+0x579>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:852
; if (have_error)
    11f9:	84 db 	testb	%bl, %bl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:863
; else if (s._message_type == max_u8)
    11fb:	0f 85 a5 00 00 00 	jne	165 <_mqtt_packet_parse+0x566>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:871
; else if (dup_flag == max_u8)
    1201:	84 d2 	testb	%dl, %dl
    1203:	0f 85 a6 01 00 00 	jne	422 <_mqtt_packet_parse+0x66f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:879
; else if (qos_flag == max_u8)
    1209:	40 84 ff 	testb	%dil, %dil
    120c:	0f 84 e9 01 00 00 	je	489 <_mqtt_packet_parse+0x6bb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:880
; error_struct =
    1212:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
    1219:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
    1220:	e9 c9 fe ff ff 	jmp	-311 <_mqtt_packet_parse+0x3ae>
    1225:	0f 1f 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1153
; ptr_variable_header_index = variable_header_index + (uint32_t)1U;
    1228:	ff 44 24 04 	incl	4(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1039
; uint8_t one_byte = request[i];
    122c:	40 88 7c 24 4e 	movb	%dil, 78(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1153
; ptr_variable_header_index = variable_header_index + (uint32_t)1U;
    1231:	31 d2 	xorl	%edx, %edx
    1233:	41 89 f3 	movl	%esi, %r11d
    1236:	e9 05 fc ff ff 	jmp	-1019 <_mqtt_packet_parse+0x100>
    123b:	0f 1f 44 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1035
; C_String_t ptr_payload = "";
    1240:	4c 8d 0d 00 00 00 00 	leaq	(%rip), %r9
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1029
; uint32_t ptr_topic_length = max_u32;
    1247:	89 4c 24 14 	movl	%ecx, 20(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1026
; uint32_t ptr_remaining_length = (uint32_t)0U;
    124b:	c7 44 24 10 00 00 00 00 	movl	$0, 16(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1036
; uint8_t ptr_payload_error_status = (uint8_t)0U;
    1253:	c6 44 24 4d 00 	movb	$0, 77(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1034
; bool ptris_searching_property_length = true;
    1258:	c6 44 24 4c 01 	movb	$1, 76(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1032
; uint8_t ptr_topic_name_error_status = (uint8_t)0U;
    125d:	c6 44 24 23 00 	movb	$0, 35(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1031
; C_String_t ptr_topic_name = "";
    1262:	4c 89 4c 24 08 	movq	%r9, 8(%rsp)
    1267:	4c 89 4c 24 18 	movq	%r9, 24(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1037
; for (uint32_t i = (uint32_t)0U; i < packet_size; i = i + (uint32_t)1U)
    126c:	45 89 f8 	movl	%r15d, %r8d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1024
; bool ptris_searching_remaining_length = true;
    126f:	ba 01 00 00 00 	movl	$1, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1022
; uint8_t ptr_fixed_header_first_one_byte = (uint8_t)0U;
    1274:	45 31 f6 	xorl	%r14d, %r14d
    1277:	e9 2c fc ff ff 	jmp	-980 <_mqtt_packet_parse+0x168>
    127c:	0f 1f 40 00 	nopl	(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:800
; return max_u8;
    1280:	84 d2 	testb	%dl, %dl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:851
; || s._payload_error_status > (uint8_t)0U;
    1282:	0f 85 58 fe ff ff 	jne	-424 <_mqtt_packet_parse+0x3a0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:844
; || s._message_type == max_u8
    1288:	45 38 d0 	cmpb	%r10b, %r8b
    128b:	0f 94 c3 	sete	%bl
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:845
; || dup_flag == max_u8
    128e:	44 38 c0 	cmpb	%r8b, %al
    1291:	0f 94 c2 	sete	%dl
    1294:	09 da 	orl	%ebx, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:844
; || s._message_type == max_u8
    1296:	41 bb 01 00 00 00 	movl	$1, %r11d
    129c:	bf 01 00 00 00 	movl	$1, %edi
    12a1:	e9 53 ff ff ff 	jmp	-173 <_mqtt_packet_parse+0x4b9>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:864
; error_struct =
    12a6:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
    12ad:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
    12b4:	e9 35 fe ff ff 	jmp	-459 <_mqtt_packet_parse+0x3ae>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:849
; || s._topic_length == max_u32
    12b9:	3b 4c 24 14 	cmpl	20(%rsp), %ecx
    12bd:	0f 84 54 01 00 00 	je	340 <_mqtt_packet_parse+0x6d7>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:851
; || s._payload_error_status > (uint8_t)0U;
    12c3:	80 7c 24 4d 00 	cmpb	$0, 77(%rsp)
    12c8:	0f 85 fe 01 00 00 	jne	510 <_mqtt_packet_parse+0x78c>
    12ce:	80 7c 24 4c 00 	cmpb	$0, 76(%rsp)
    12d3:	74 1b 	je	27 <_mqtt_packet_parse+0x5b0>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:912
; error_struct =
    12d5:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
    12dc:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
    12e3:	e9 06 fe ff ff 	jmp	-506 <_mqtt_packet_parse+0x3ae>
    12e8:	0f 1f 84 00 00 00 00 00 	nopl	(%rax,%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:852
; if (have_error)
    12f0:	41 88 44 24 11 	movb	%al, 17(%r12)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:933
; (
    12f5:	8b 44 24 10 	movl	16(%rsp), %eax
    12f9:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    1300:	41 89 44 24 14 	movl	%eax, 20(%r12)
    1305:	8b 44 24 14 	movl	20(%rsp), %eax
    1309:	45 88 14 24 	movb	%r10b, (%r12)
    130d:	41 89 44 24 18 	movl	%eax, 24(%r12)
    1312:	48 8b 44 24 18 	movq	24(%rsp), %rax
    1317:	49 89 54 24 08 	movq	%rdx, 8(%r12)
    131c:	49 89 44 24 20 	movq	%rax, 32(%r12)
    1321:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    1328:	45 88 44 24 10 	movb	%r8b, 16(%r12)
    132d:	41 88 44 24 38 	movb	%al, 56(%r12)
    1332:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
    1339:	41 88 74 24 12 	movb	%sil, 18(%r12)
    133e:	45 88 74 24 13 	movb	%r14b, 19(%r12)
    1343:	41 c7 44 24 28 00 00 00 00 	movl	$0, 40(%r12)
    134c:	4d 89 4c 24 30 	movq	%r9, 48(%r12)
    1351:	49 89 44 24 40 	movq	%rax, 64(%r12)
    1356:	e9 cb fc ff ff 	jmp	-821 <_mqtt_packet_parse+0x2e6>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1077
; uint8_t msb_u8 = ptr_for_topic_length;
    135b:	0f b6 44 24 4e 	movzbl	78(%rsp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1081
; uint32_t _topic_length = msb_u32 << (uint32_t)8U | lsb_u32;
    1360:	c1 e0 08 	shll	$8, %eax
    1363:	09 f8 	orl	%edi, %eax
    1365:	89 44 24 14 	movl	%eax, 20(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1082
; if (_topic_length > (uint32_t)65535U)
    1369:	e9 ad fb ff ff 	jmp	-1107 <_mqtt_packet_parse+0x1db>
    136e:	66 90 	nop
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:965
; if (have_error)
    1370:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:985
; error_struct =
    1377:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:976
; else if (s._message_type == max_u8)
    137e:	45 38 f8 	cmpb	%r15b, %r8b
    1381:	0f 85 5a fc ff ff 	jne	-934 <_mqtt_packet_parse+0x2a1>
    1387:	e9 c4 fd ff ff 	jmp	-572 <_mqtt_packet_parse+0x410>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1116
; else if
    138c:	8b 54 24 14 	movl	20(%rsp), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1120
; && variable_header_index <= topic_length + (uint32_t)5U
    1390:	83 c2 05 	addl	$5, %edx
    1393:	3b 54 24 04 	cmpl	4(%rsp), %edx
    1397:	72 29 	jb	41 <_mqtt_packet_parse+0x682>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1121
; && is_searching_property_length
    1399:	80 7c 24 4c 00 	cmpb	$0, 76(%rsp)
    139e:	74 2f 	je	47 <_mqtt_packet_parse+0x68f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1124
; if (one_byte == (uint8_t)0U)
    13a0:	40 84 ff 	testb	%dil, %dil
    13a3:	0f 95 44 24 4c 	setne	76(%rsp)
    13a8:	31 f6 	xorl	%esi, %esi
    13aa:	e9 6c fb ff ff 	jmp	-1172 <_mqtt_packet_parse+0x1db>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:872
; error_struct =
    13af:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
    13b6:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
    13bd:	e9 2c fd ff ff 	jmp	-724 <_mqtt_packet_parse+0x3ae>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1130
; else if (!is_searching_property_length)
    13c2:	31 f6 	xorl	%esi, %esi
    13c4:	80 7c 24 4c 00 	cmpb	$0, 76(%rsp)
    13c9:	0f 85 4c fb ff ff 	jne	-1204 <_mqtt_packet_parse+0x1db>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1132
; uint32_t payload_offset = i;
    13cf:	8b 54 24 48 	movl	72(%rsp), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1135
; uint8_t last_payload_element = ptr_payload_u8[last_payload_index];
    13d3:	44 29 ea 	subl	%r13d, %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1137
; if (last_payload_element != (uint8_t)0U)
    13d6:	80 3c 10 00 	cmpb	$0, (%rax,%rdx)
    13da:	0f 84 8d 00 00 00 	je	141 <_mqtt_packet_parse+0x72d>
    13e0:	c6 44 24 4c 00 	movb	$0, 76(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1139
; ptr_payload_error_status = (uint8_t)1U;
    13e5:	c6 44 24 4d 01 	movb	$1, 77(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1140
; payload = "";
    13ea:	4c 8d 0d 00 00 00 00 	leaq	(%rip), %r9
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1149
; ptr_is_break = true;
    13f1:	be 01 00 00 00 	movl	$1, %esi
    13f6:	e9 20 fb ff ff 	jmp	-1248 <_mqtt_packet_parse+0x1db>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:887
; else if (retain_flag == max_u8)
    13fb:	45 84 db 	testb	%r11b, %r11b
    13fe:	0f 84 ab 00 00 00 	je	171 <_mqtt_packet_parse+0x76f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:888
; error_struct =
    1404:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
    140b:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
    1412:	e9 d7 fc ff ff 	jmp	-809 <_mqtt_packet_parse+0x3ae>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:896
; error_struct =
    1417:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
    141e:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
    1425:	e9 c4 fc ff ff 	jmp	-828 <_mqtt_packet_parse+0x3ae>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1107
; topic_name = Utils_topic_name_uint8_to_c_string(ptr_topic_name_u8);
    142a:	48 8d bc 24 80 00 00 00 	leaq	128(%rsp), %rdi
    1432:	4c 89 44 24 38 	movq	%r8, 56(%rsp)
    1437:	4c 89 4c 24 30 	movq	%r9, 48(%rsp)
    143c:	40 88 74 24 28 	movb	%sil, 40(%rsp)
    1441:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x706>
    1446:	48 89 44 24 18 	movq	%rax, 24(%rsp)
    144b:	8b 0d 00 00 00 00 	movl	(%rip), %ecx
    1451:	44 0f b6 15 00 00 00 00 	movzbl	(%rip), %r10d
    1459:	0f b6 74 24 28 	movzbl	40(%rsp), %esi
    145e:	4c 8b 4c 24 30 	movq	48(%rsp), %r9
    1463:	4c 8b 44 24 38 	movq	56(%rsp), %r8
    1468:	e9 ae fa ff ff 	jmp	-1362 <_mqtt_packet_parse+0x1db>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1144
; Utils_payload_uint8_to_c_string(ptr_payload_u8,
    146d:	8b 4c 24 48 	movl	72(%rsp), %ecx
    1471:	8b 35 00 00 00 00 	movl	(%rip), %esi
    1477:	8b 15 00 00 00 00 	movl	(%rip), %edx
    147d:	48 89 c7 	movq	%rax, %rdi
    1480:	4c 89 44 24 28 	movq	%r8, 40(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1143
; payload =
    1485:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x74a>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1144
; Utils_payload_uint8_to_c_string(ptr_payload_u8,
    148a:	49 89 c1 	movq	%rax, %r9
    148d:	c6 44 24 4c 00 	movb	$0, 76(%rsp)
    1492:	8b 0d 00 00 00 00 	movl	(%rip), %ecx
    1498:	44 0f b6 15 00 00 00 00 	movzbl	(%rip), %r10d
    14a0:	4c 8b 44 24 28 	movq	40(%rsp), %r8
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1149
; ptr_is_break = true;
    14a5:	be 01 00 00 00 	movl	$1, %esi
    14aa:	e9 6c fa ff ff 	jmp	-1428 <_mqtt_packet_parse+0x1db>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:895
; else if (s._topic_length == max_u32)
    14af:	3b 4c 24 14 	cmpl	20(%rsp), %ecx
    14b3:	0f 84 5e ff ff ff 	je	-162 <_mqtt_packet_parse+0x6d7>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:904
; error_struct =
    14b9:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
    14c0:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
    14c7:	e9 22 fc ff ff 	jmp	-990 <_mqtt_packet_parse+0x3ae>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:895
; else if (s._topic_length == max_u32)
    14cc:	80 7c 24 4c 00 	cmpb	$0, 76(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:920
; error_struct =
    14d1:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
    14d8:	48 8b 05 00 00 00 00 	movq	(%rip), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:911
; else if (s.is_searching_property_length)
    14df:	0f 84 09 fc ff ff 	je	-1015 <_mqtt_packet_parse+0x3ae>
    14e5:	e9 eb fd ff ff 	jmp	-533 <_mqtt_packet_parse+0x595>
