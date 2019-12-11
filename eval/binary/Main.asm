
Main.o:	file format Mach-O 64-bit x86-64

Disassembly of section __TEXT,__text:
_new_line:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:171
; {
       0:	55 	pushq	%rbp
       1:	48 89 e5 	movq	%rsp, %rbp
       4:	48 83 8c 24 00 f0 ff ff 00 	orq	$0, -4096(%rsp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:172
; LowStar_Printf_print_string("\n");
       d:	48 8d 3d 00 00 00 00 	leaq	(%rip), %rdi
      14:	e8 00 00 00 00 	callq	0 <_new_line+0x19>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:173
; }
      19:	90 	nop
      1a:	5d 	popq	%rbp
      1b:	c3 	retq

_slice_byte:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:176
; {
      1c:	55 	pushq	%rbp
      1d:	48 89 e5 	movq	%rsp, %rbp
      20:	89 f1 	movl	%esi, %ecx
      22:	89 d0 	movl	%edx, %eax
      24:	89 fa 	movl	%edi, %edx
      26:	88 55 ec 	movb	%dl, -20(%rbp)
      29:	89 ca 	movl	%ecx, %edx
      2b:	88 55 e8 	movb	%dl, -24(%rbp)
      2e:	88 45 e4 	movb	%al, -28(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:178
; if ((uint32_t)0U == (uint32_t)a)
      31:	80 7d e8 00 	cmpb	$0, -24(%rbp)
      35:	75 06 	jne	6 <_slice_byte+0x21>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:179
; for_mask_temp1 = (uint8_t)0b11111111U;
      37:	c6 45 ff ff 	movb	$-1, -1(%rbp)
      3b:	eb 4c 	jmp	76 <_slice_byte+0x6d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:180
; else if ((uint32_t)1U == (uint32_t)a)
      3d:	80 7d e8 01 	cmpb	$1, -24(%rbp)
      41:	75 06 	jne	6 <_slice_byte+0x2d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:181
; for_mask_temp1 = (uint8_t)0b01111111U;
      43:	c6 45 ff 7f 	movb	$127, -1(%rbp)
      47:	eb 40 	jmp	64 <_slice_byte+0x6d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:182
; else if ((uint32_t)2U == (uint32_t)a)
      49:	80 7d e8 02 	cmpb	$2, -24(%rbp)
      4d:	75 06 	jne	6 <_slice_byte+0x39>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:183
; for_mask_temp1 = (uint8_t)0b00111111U;
      4f:	c6 45 ff 3f 	movb	$63, -1(%rbp)
      53:	eb 34 	jmp	52 <_slice_byte+0x6d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:184
; else if ((uint32_t)3U == (uint32_t)a)
      55:	80 7d e8 03 	cmpb	$3, -24(%rbp)
      59:	75 06 	jne	6 <_slice_byte+0x45>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:185
; for_mask_temp1 = (uint8_t)0b00011111U;
      5b:	c6 45 ff 1f 	movb	$31, -1(%rbp)
      5f:	eb 28 	jmp	40 <_slice_byte+0x6d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:186
; else if ((uint32_t)4U == (uint32_t)a)
      61:	80 7d e8 04 	cmpb	$4, -24(%rbp)
      65:	75 06 	jne	6 <_slice_byte+0x51>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:187
; for_mask_temp1 = (uint8_t)0b00001111U;
      67:	c6 45 ff 0f 	movb	$15, -1(%rbp)
      6b:	eb 1c 	jmp	28 <_slice_byte+0x6d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:188
; else if ((uint32_t)5U == (uint32_t)a)
      6d:	80 7d e8 05 	cmpb	$5, -24(%rbp)
      71:	75 06 	jne	6 <_slice_byte+0x5d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:189
; for_mask_temp1 = (uint8_t)0b00000111U;
      73:	c6 45 ff 07 	movb	$7, -1(%rbp)
      77:	eb 10 	jmp	16 <_slice_byte+0x6d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:190
; else if ((uint32_t)6U == (uint32_t)a)
      79:	80 7d e8 06 	cmpb	$6, -24(%rbp)
      7d:	75 06 	jne	6 <_slice_byte+0x69>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:191
; for_mask_temp1 = (uint8_t)0b00000011U;
      7f:	c6 45 ff 03 	movb	$3, -1(%rbp)
      83:	eb 04 	jmp	4 <_slice_byte+0x6d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:193
; for_mask_temp1 = (uint8_t)0b00000001U;
      85:	c6 45 ff 01 	movb	$1, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:195
; if ((uint32_t)1U == (uint32_t)b)
      89:	80 7d e4 01 	cmpb	$1, -28(%rbp)
      8d:	75 06 	jne	6 <_slice_byte+0x79>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:196
; for_mask_temp2 = (uint8_t)0b10000000U;
      8f:	c6 45 fe 80 	movb	$-128, -2(%rbp)
      93:	eb 4c 	jmp	76 <_slice_byte+0xc5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:197
; else if ((uint32_t)2U == (uint32_t)b)
      95:	80 7d e4 02 	cmpb	$2, -28(%rbp)
      99:	75 06 	jne	6 <_slice_byte+0x85>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:198
; for_mask_temp2 = (uint8_t)0b11000000U;
      9b:	c6 45 fe c0 	movb	$-64, -2(%rbp)
      9f:	eb 40 	jmp	64 <_slice_byte+0xc5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:199
; else if ((uint32_t)3U == (uint32_t)b)
      a1:	80 7d e4 03 	cmpb	$3, -28(%rbp)
      a5:	75 06 	jne	6 <_slice_byte+0x91>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:200
; for_mask_temp2 = (uint8_t)0b11100000U;
      a7:	c6 45 fe e0 	movb	$-32, -2(%rbp)
      ab:	eb 34 	jmp	52 <_slice_byte+0xc5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:201
; else if ((uint32_t)4U == (uint32_t)b)
      ad:	80 7d e4 04 	cmpb	$4, -28(%rbp)
      b1:	75 06 	jne	6 <_slice_byte+0x9d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:202
; for_mask_temp2 = (uint8_t)0b11110000U;
      b3:	c6 45 fe f0 	movb	$-16, -2(%rbp)
      b7:	eb 28 	jmp	40 <_slice_byte+0xc5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:203
; else if ((uint32_t)5U == (uint32_t)b)
      b9:	80 7d e4 05 	cmpb	$5, -28(%rbp)
      bd:	75 06 	jne	6 <_slice_byte+0xa9>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:204
; for_mask_temp2 = (uint8_t)0b11111000U;
      bf:	c6 45 fe f8 	movb	$-8, -2(%rbp)
      c3:	eb 1c 	jmp	28 <_slice_byte+0xc5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:205
; else if ((uint32_t)6U == (uint32_t)b)
      c5:	80 7d e4 06 	cmpb	$6, -28(%rbp)
      c9:	75 06 	jne	6 <_slice_byte+0xb5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:206
; for_mask_temp2 = (uint8_t)0b11111100U;
      cb:	c6 45 fe fc 	movb	$-4, -2(%rbp)
      cf:	eb 10 	jmp	16 <_slice_byte+0xc5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:207
; else if ((uint32_t)7U == (uint32_t)b)
      d1:	80 7d e4 07 	cmpb	$7, -28(%rbp)
      d5:	75 06 	jne	6 <_slice_byte+0xc1>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:208
; for_mask_temp2 = (uint8_t)0b11111110U;
      d7:	c6 45 fe fe 	movb	$-2, -2(%rbp)
      db:	eb 04 	jmp	4 <_slice_byte+0xc5>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:210
; for_mask_temp2 = (uint8_t)0b11111111U;
      dd:	c6 45 fe ff 	movb	$-1, -2(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:211
; uint8_t mask = for_mask_temp1 & for_mask_temp2;
      e1:	0f b6 45 ff 	movzbl	-1(%rbp), %eax
      e5:	22 45 fe 	andb	-2(%rbp), %al
      e8:	88 45 fd 	movb	%al, -3(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:212
; return (byte & mask) >> (uint32_t)8U - (uint32_t)b;
      eb:	0f b6 45 ec 	movzbl	-20(%rbp), %eax
      ef:	22 45 fd 	andb	-3(%rbp), %al
      f2:	0f b6 d0 	movzbl	%al, %edx
      f5:	0f b6 45 e4 	movzbl	-28(%rbp), %eax
      f9:	b9 08 00 00 00 	movl	$8, %ecx
      fe:	29 c1 	subl	%eax, %ecx
     100:	89 c8 	movl	%ecx, %eax
     102:	89 c1 	movl	%eax, %ecx
     104:	d3 fa 	sarl	%cl, %edx
     106:	89 d0 	movl	%edx, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:213
; }
     108:	5d 	popq	%rbp
     109:	c3 	retq

_is_valid_decoding_packet_check:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:216
; {
     10a:	55 	pushq	%rbp
     10b:	48 89 e5 	movq	%rsp, %rbp
     10e:	48 89 7d d8 	movq	%rdi, -40(%rbp)
     112:	89 f0 	movl	%esi, %eax
     114:	88 45 d4 	movb	%al, -44(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:217
; uint8_t ptr_status = (uint8_t)0U;
     117:	c6 45 ff 00 	movb	$0, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:218
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     11b:	c7 45 f8 00 00 00 00 	movl	$0, -8(%rbp)
     122:	e9 82 00 00 00 	jmp	130 <_is_valid_decoding_packet_check+0x9f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:220
; uint8_t ptr_status_v = ptr_status;
     127:	0f b6 45 ff 	movzbl	-1(%rbp), %eax
     12b:	88 45 f6 	movb	%al, -10(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:221
; uint32_t bytes_length_u32 = (uint32_t)bytes_length;
     12e:	0f b6 45 d4 	movzbl	-44(%rbp), %eax
     132:	89 45 f0 	movl	%eax, -16(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:222
; if (ptr_status_v == (uint8_t)0U)
     135:	80 7d f6 00 	cmpb	$0, -10(%rbp)
     139:	75 6a 	jne	106 <_is_valid_decoding_packet_check+0x9b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:223
; if (i < bytes_length_u32)
     13b:	8b 45 f8 	movl	-8(%rbp), %eax
     13e:	3b 45 f0 	cmpl	-16(%rbp), %eax
     141:	73 62 	jae	98 <_is_valid_decoding_packet_check+0x9b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:225
; uint8_t decoding_packet = ptr_for_decoding_packets[i];
     143:	8b 45 f8 	movl	-8(%rbp), %eax
     146:	48 8b 55 d8 	movq	-40(%rbp), %rdx
     14a:	48 01 d0 	addq	%rdx, %rax
     14d:	0f b6 00 	movzbl	(%rax), %eax
     150:	88 45 ef 	movb	%al, -17(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:226
; if (bytes_length == (uint8_t)1U)
     153:	80 7d d4 01 	cmpb	$1, -44(%rbp)
     157:	75 0e 	jne	14 <_is_valid_decoding_packet_check+0x5d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:228
; if (decoding_packet < (uint8_t)0U || decoding_packet > (uint8_t)127U)
     159:	0f b6 45 ef 	movzbl	-17(%rbp), %eax
     15d:	84 c0 	testb	%al, %al
     15f:	79 44 	jns	68 <_is_valid_decoding_packet_check+0x9b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:229
; ptr_status = (uint8_t)1U;
     161:	c6 45 ff 01 	movb	$1, -1(%rbp)
     165:	eb 3e 	jmp	62 <_is_valid_decoding_packet_check+0x9b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:233
; uint32_t data_length_minus_one = (uint32_t)(bytes_length - (uint8_t)1U);
     167:	0f b6 45 d4 	movzbl	-44(%rbp), %eax
     16b:	83 e8 01 	subl	$1, %eax
     16e:	89 45 e8 	movl	%eax, -24(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:234
; if (i == data_length_minus_one)
     171:	8b 45 f8 	movl	-8(%rbp), %eax
     174:	3b 45 e8 	cmpl	-24(%rbp), %eax
     177:	75 14 	jne	20 <_is_valid_decoding_packet_check+0x83>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:236
; if (decoding_packet < (uint8_t)1U || decoding_packet > (uint8_t)127U)
     179:	80 7d ef 00 	cmpb	$0, -17(%rbp)
     17d:	74 08 	je	8 <_is_valid_decoding_packet_check+0x7d>
     17f:	0f b6 45 ef 	movzbl	-17(%rbp), %eax
     183:	84 c0 	testb	%al, %al
     185:	79 1e 	jns	30 <_is_valid_decoding_packet_check+0x9b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:237
; ptr_status = (uint8_t)2U;
     187:	c6 45 ff 02 	movb	$2, -1(%rbp)
     18b:	eb 18 	jmp	24 <_is_valid_decoding_packet_check+0x9b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:239
; else if (decoding_packet < (uint8_t)128U || decoding_packet > max_u8)
     18d:	0f b6 45 ef 	movzbl	-17(%rbp), %eax
     191:	84 c0 	testb	%al, %al
     193:	79 0c 	jns	12 <_is_valid_decoding_packet_check+0x97>
     195:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     19c:	38 45 ef 	cmpb	%al, -17(%rbp)
     19f:	76 04 	jbe	4 <_is_valid_decoding_packet_check+0x9b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:240
; ptr_status = (uint8_t)3U;
     1a1:	c6 45 ff 03 	movb	$3, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:218
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     1a5:	83 45 f8 01 	addl	$1, -8(%rbp)
     1a9:	83 7d f8 03 	cmpl	$3, -8(%rbp)
     1ad:	0f 86 74 ff ff ff 	jbe	-140 <_is_valid_decoding_packet_check+0x1d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:244
; uint8_t r = ptr_status;
     1b3:	0f b6 45 ff 	movzbl	-1(%rbp), %eax
     1b7:	88 45 f7 	movb	%al, -9(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:245
; return r;
     1ba:	0f b6 45 f7 	movzbl	-9(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:246
; }
     1be:	5d 	popq	%rbp
     1bf:	c3 	retq

_most_significant_four_bit_to_zero:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:249
; {
     1c0:	55 	pushq	%rbp
     1c1:	48 89 e5 	movq	%rsp, %rbp
     1c4:	89 f8 	movl	%edi, %eax
     1c6:	88 45 fc 	movb	%al, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:250
; if (i >= (uint8_t)128U)
     1c9:	0f b6 45 fc 	movzbl	-4(%rbp), %eax
     1cd:	84 c0 	testb	%al, %al
     1cf:	79 09 	jns	9 <_most_significant_four_bit_to_zero+0x1a>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:251
; return i - (uint8_t)128U;
     1d1:	0f b6 45 fc 	movzbl	-4(%rbp), %eax
     1d5:	83 c0 80 	addl	$-128, %eax
     1d8:	eb 04 	jmp	4 <_most_significant_four_bit_to_zero+0x1e>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:253
; return i;
     1da:	0f b6 45 fc 	movzbl	-4(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:254
; }
     1de:	5d 	popq	%rbp
     1df:	c3 	retq

_except_most_significant_four_bit_to_zero:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:257
; {
     1e0:	55 	pushq	%rbp
     1e1:	48 89 e5 	movq	%rsp, %rbp
     1e4:	89 f8 	movl	%edi, %eax
     1e6:	88 45 fc 	movb	%al, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:258
; if (i <= (uint8_t)127U)
     1e9:	0f b6 45 fc 	movzbl	-4(%rbp), %eax
     1ed:	84 c0 	testb	%al, %al
     1ef:	78 07 	js	7 <_except_most_significant_four_bit_to_zero+0x18>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:259
; return (uint8_t)0U;
     1f1:	b8 00 00 00 00 	movl	$0, %eax
     1f6:	eb 05 	jmp	5 <_except_most_significant_four_bit_to_zero+0x1d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:261
; return (uint8_t)128U;
     1f8:	b8 80 ff ff ff 	movl	$4294967168, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:262
; }
     1fd:	5d 	popq	%rbp
     1fe:	c3 	retq

_decodeing_variable_bytes:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:265
; {
     1ff:	55 	pushq	%rbp
     200:	48 89 e5 	movq	%rsp, %rbp
     203:	48 83 8c 24 b0 ef ff ff 00 	orq	$0, -4176(%rsp)
     20c:	48 83 ec 50 	subq	$80, %rsp
     210:	48 89 7d b8 	movq	%rdi, -72(%rbp)
     214:	89 f0 	movl	%esi, %eax
     216:	88 45 b4 	movb	%al, -76(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:266
; uint8_t ptr_for_decoding_packet = (uint8_t)0U;
     219:	c6 45 e7 00 	movb	$0, -25(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:267
; uint32_t ptr_for_remaining_length = (uint32_t)0U;
     21d:	c7 45 fc 00 00 00 00 	movl	$0, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:268
; uint8_t ptr_status = (uint8_t)1U;
     224:	c6 45 fb 01 	movb	$1, -5(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:269
; uint32_t ptr_temp1 = (uint32_t)0U;
     228:	c7 45 f4 00 00 00 00 	movl	$0, -12(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:270
; uint32_t ptr_temp2 = (uint32_t)0U;
     22f:	c7 45 f0 00 00 00 00 	movl	$0, -16(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:271
; uint32_t ptr_temp3 = (uint32_t)0U;
     236:	c7 45 ec 00 00 00 00 	movl	$0, -20(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:272
; uint32_t ptr_temp4 = (uint32_t)0U;
     23d:	c7 45 e0 00 00 00 00 	movl	$0, -32(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:275
; is_valid_decoding_packet_check(ptr_for_decoding_packets,
     244:	0f b6 45 b4 	movzbl	-76(%rbp), %eax
     248:	48 8b 55 b8 	movq	-72(%rbp), %rdx
     24c:	89 c6 	movl	%eax, %esi
     24e:	48 89 d7 	movq	%rdx, %rdi
     251:	e8 00 00 00 00 	callq	0 <_decodeing_variable_bytes+0x57>
     256:	88 45 df 	movb	%al, -33(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:277
; if (is_valid_decoding_packet != (uint8_t)0U)
     259:	80 7d df 00 	cmpb	$0, -33(%rbp)
     25d:	74 0b 	je	11 <_decodeing_variable_bytes+0x6b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:278
; return max_u32;
     25f:	8b 05 00 00 00 00 	movl	(%rip), %eax
     265:	e9 d7 00 00 00 	jmp	215 <_decodeing_variable_bytes+0x142>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:281
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     26a:	c7 45 e8 00 00 00 00 	movl	$0, -24(%rbp)
     271:	e9 b8 00 00 00 	jmp	184 <_decodeing_variable_bytes+0x12f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:283
; uint8_t ptr_status_v = ptr_status;
     276:	0f b6 45 fb 	movzbl	-5(%rbp), %eax
     27a:	88 45 d7 	movb	%al, -41(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:284
; if (ptr_status_v == (uint8_t)1U)
     27d:	80 7d d7 01 	cmpb	$1, -41(%rbp)
     281:	0f 85 a3 00 00 00 	jne	163 <_decodeing_variable_bytes+0x12b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:286
; uint8_t decoding_packet = ptr_for_decoding_packets[i];
     287:	8b 45 e8 	movl	-24(%rbp), %eax
     28a:	48 8b 55 b8 	movq	-72(%rbp), %rdx
     28e:	48 01 d0 	addq	%rdx, %rax
     291:	0f b6 00 	movzbl	(%rax), %eax
     294:	88 45 d6 	movb	%al, -42(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:287
; uint8_t b_u8 = most_significant_four_bit_to_zero(decoding_packet);
     297:	0f b6 45 d6 	movzbl	-42(%rbp), %eax
     29b:	89 c7 	movl	%eax, %edi
     29d:	e8 00 00 00 00 	callq	0 <_decodeing_variable_bytes+0xa3>
     2a2:	88 45 d5 	movb	%al, -43(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:288
; uint32_t b_u32 = (uint32_t)b_u8;
     2a5:	0f b6 45 d5 	movzbl	-43(%rbp), %eax
     2a9:	89 45 d0 	movl	%eax, -48(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:289
; uint8_t b2_u8 = except_most_significant_four_bit_to_zero(decoding_packet);
     2ac:	0f b6 45 d6 	movzbl	-42(%rbp), %eax
     2b0:	89 c7 	movl	%eax, %edi
     2b2:	e8 00 00 00 00 	callq	0 <_decodeing_variable_bytes+0xb8>
     2b7:	88 45 cf 	movb	%al, -49(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:290
; if (i == (uint32_t)0U)
     2ba:	83 7d e8 00 	cmpl	$0, -24(%rbp)
     2be:	75 0e 	jne	14 <_decodeing_variable_bytes+0xcf>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:292
; ptr_temp1 = b_u32 * (uint32_t)1U;
     2c0:	8b 45 d0 	movl	-48(%rbp), %eax
     2c3:	89 45 f4 	movl	%eax, -12(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:293
; ptr_for_remaining_length = ptr_temp1;
     2c6:	8b 45 f4 	movl	-12(%rbp), %eax
     2c9:	89 45 fc 	movl	%eax, -4(%rbp)
     2cc:	eb 52 	jmp	82 <_decodeing_variable_bytes+0x121>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:295
; else if (i == (uint32_t)1U)
     2ce:	83 7d e8 01 	cmpl	$1, -24(%rbp)
     2d2:	75 18 	jne	24 <_decodeing_variable_bytes+0xed>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:297
; ptr_temp2 = ptr_temp1 + b_u32 * (uint32_t)128U;
     2d4:	8b 45 d0 	movl	-48(%rbp), %eax
     2d7:	c1 e0 07 	shll	$7, %eax
     2da:	89 c2 	movl	%eax, %edx
     2dc:	8b 45 f4 	movl	-12(%rbp), %eax
     2df:	01 d0 	addl	%edx, %eax
     2e1:	89 45 f0 	movl	%eax, -16(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:298
; ptr_for_remaining_length = ptr_temp2;
     2e4:	8b 45 f0 	movl	-16(%rbp), %eax
     2e7:	89 45 fc 	movl	%eax, -4(%rbp)
     2ea:	eb 34 	jmp	52 <_decodeing_variable_bytes+0x121>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:300
; else if (i == (uint32_t)2U)
     2ec:	83 7d e8 02 	cmpl	$2, -24(%rbp)
     2f0:	75 18 	jne	24 <_decodeing_variable_bytes+0x10b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:302
; ptr_temp3 = ptr_temp2 + b_u32 * (uint32_t)128U * (uint32_t)128U;
     2f2:	8b 45 d0 	movl	-48(%rbp), %eax
     2f5:	c1 e0 0e 	shll	$14, %eax
     2f8:	89 c2 	movl	%eax, %edx
     2fa:	8b 45 f0 	movl	-16(%rbp), %eax
     2fd:	01 d0 	addl	%edx, %eax
     2ff:	89 45 ec 	movl	%eax, -20(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:303
; ptr_for_remaining_length = ptr_temp3;
     302:	8b 45 ec 	movl	-20(%rbp), %eax
     305:	89 45 fc 	movl	%eax, -4(%rbp)
     308:	eb 16 	jmp	22 <_decodeing_variable_bytes+0x121>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:307
; ptr_temp4 = ptr_temp3 + b_u32 * (uint32_t)128U * (uint32_t)128U * (uint32_t)128U;
     30a:	8b 45 d0 	movl	-48(%rbp), %eax
     30d:	c1 e0 15 	shll	$21, %eax
     310:	89 c2 	movl	%eax, %edx
     312:	8b 45 ec 	movl	-20(%rbp), %eax
     315:	01 d0 	addl	%edx, %eax
     317:	89 45 e0 	movl	%eax, -32(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:308
; ptr_for_remaining_length = ptr_temp4;
     31a:	8b 45 e0 	movl	-32(%rbp), %eax
     31d:	89 45 fc 	movl	%eax, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:310
; if (b2_u8 == (uint8_t)0U)
     320:	80 7d cf 00 	cmpb	$0, -49(%rbp)
     324:	75 04 	jne	4 <_decodeing_variable_bytes+0x12b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:311
; ptr_status = (uint8_t)0U;
     326:	c6 45 fb 00 	movb	$0, -5(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:281
; for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
     32a:	83 45 e8 01 	addl	$1, -24(%rbp)
     32e:	83 7d e8 03 	cmpl	$3, -24(%rbp)
     332:	0f 86 3e ff ff ff 	jbe	-194 <_decodeing_variable_bytes+0x77>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:314
; uint32_t remaining_length = ptr_for_remaining_length;
     338:	8b 45 fc 	movl	-4(%rbp), %eax
     33b:	89 45 d8 	movl	%eax, -40(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:315
; return remaining_length;
     33e:	8b 45 d8 	movl	-40(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:317
; }
     341:	c9 	leave
     342:	c3 	retq

_get_remaining_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:325
; {
     343:	55 	pushq	%rbp
     344:	48 89 e5 	movq	%rsp, %rbp
     347:	48 83 8c 24 e0 ef ff ff 00 	orq	$0, -4128(%rsp)
     350:	48 83 ec 20 	subq	$32, %rsp
     354:	89 f8 	movl	%edi, %eax
     356:	48 89 75 e0 	movq	%rsi, -32(%rbp)
     35a:	89 55 e8 	movl	%edx, -24(%rbp)
     35d:	88 45 ec 	movb	%al, -20(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:326
; uint32_t fixed_value = packet_size - (uint32_t)1U;
     360:	8b 45 e8 	movl	-24(%rbp), %eax
     363:	83 e8 01 	subl	$1, %eax
     366:	89 45 fc 	movl	%eax, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:327
; uint32_t bytes_length_u32 = (uint32_t)bytes_length;
     369:	0f b6 45 ec 	movzbl	-20(%rbp), %eax
     36d:	89 45 f8 	movl	%eax, -8(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:328
; uint32_t untrust_r = decodeing_variable_bytes(ptr_for_decoding_packets, bytes_length);
     370:	0f b6 45 ec 	movzbl	-20(%rbp), %eax
     374:	48 8b 55 e0 	movq	-32(%rbp), %rdx
     378:	89 c6 	movl	%eax, %esi
     37a:	48 89 d7 	movq	%rdx, %rdi
     37d:	e8 00 00 00 00 	callq	0 <_get_remaining_length+0x3f>
     382:	89 45 f4 	movl	%eax, -12(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:329
; if (untrust_r != max_u32)
     385:	8b 05 00 00 00 00 	movl	(%rip), %eax
     38b:	39 45 f4 	cmpl	%eax, -12(%rbp)
     38e:	74 1a 	je	26 <_get_remaining_length+0x67>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:330
; if (bytes_length_u32 + untrust_r == fixed_value)
     390:	8b 55 f8 	movl	-8(%rbp), %edx
     393:	8b 45 f4 	movl	-12(%rbp), %eax
     396:	01 d0 	addl	%edx, %eax
     398:	39 45 fc 	cmpl	%eax, -4(%rbp)
     39b:	75 05 	jne	5 <_get_remaining_length+0x5f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:331
; return untrust_r;
     39d:	8b 45 f4 	movl	-12(%rbp), %eax
     3a0:	eb 0e 	jmp	14 <_get_remaining_length+0x6d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:333
; return max_u32;
     3a2:	8b 05 00 00 00 00 	movl	(%rip), %eax
     3a8:	eb 06 	jmp	6 <_get_remaining_length+0x6d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:335
; return max_u32;
     3aa:	8b 05 00 00 00 00 	movl	(%rip), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:336
; }
     3b0:	c9 	leave
     3b1:	c3 	retq

_get_message_type:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:339
; {
     3b2:	55 	pushq	%rbp
     3b3:	48 89 e5 	movq	%rsp, %rbp
     3b6:	89 f8 	movl	%edi, %eax
     3b8:	88 45 fc 	movb	%al, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:340
; if (message_type_bits < (uint8_t)1U || message_type_bits > (uint8_t)15U)
     3bb:	80 7d fc 00 	cmpb	$0, -4(%rbp)
     3bf:	74 06 	je	6 <_get_message_type+0x15>
     3c1:	80 7d fc 0f 	cmpb	$15, -4(%rbp)
     3c5:	76 09 	jbe	9 <_get_message_type+0x1e>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:341
; return max_u8;
     3c7:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     3ce:	eb 04 	jmp	4 <_get_message_type+0x22>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:343
; return message_type_bits;
     3d0:	0f b6 45 fc 	movzbl	-4(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:344
; }
     3d4:	5d 	popq	%rbp
     3d5:	c3 	retq

___proj__Mkstruct_flags__item__flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:347
; {
     3d6:	55 	pushq	%rbp
     3d7:	48 89 e5 	movq	%rsp, %rbp
     3da:	89 7d fc 	movl	%edi, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:348
; return projectee.flag;
     3dd:	0f b6 45 fc 	movzbl	-4(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:349
; }
     3e1:	5d 	popq	%rbp
     3e2:	c3 	retq

___proj__Mkstruct_flags__item__dup_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:352
; {
     3e3:	55 	pushq	%rbp
     3e4:	48 89 e5 	movq	%rsp, %rbp
     3e7:	89 7d fc 	movl	%edi, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:353
; return projectee.dup_flag;
     3ea:	0f b6 45 fd 	movzbl	-3(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:354
; }
     3ee:	5d 	popq	%rbp
     3ef:	c3 	retq

___proj__Mkstruct_flags__item__qos_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:357
; {
     3f0:	55 	pushq	%rbp
     3f1:	48 89 e5 	movq	%rsp, %rbp
     3f4:	89 7d fc 	movl	%edi, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:358
; return projectee.qos_flag;
     3f7:	0f b6 45 fe 	movzbl	-2(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:359
; }
     3fb:	5d 	popq	%rbp
     3fc:	c3 	retq

___proj__Mkstruct_flags__item__retain_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:362
; {
     3fd:	55 	pushq	%rbp
     3fe:	48 89 e5 	movq	%rsp, %rbp
     401:	89 7d fc 	movl	%edi, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:363
; return projectee.retain_flag;
     404:	0f b6 45 ff 	movzbl	-1(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:364
; }
     408:	5d 	popq	%rbp
     409:	c3 	retq

___proj__Mkstruct_fixed_header_constant__item__message_type_constant:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:370
; {
     40a:	55 	pushq	%rbp
     40b:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:371
; return projectee.message_type_constant;
     40e:	0f b6 45 10 	movzbl	16(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:372
; }
     412:	5d 	popq	%rbp
     413:	c3 	retq

___proj__Mkstruct_fixed_header_constant__item__message_name_constant:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:378
; {
     414:	55 	pushq	%rbp
     415:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:379
; return projectee.message_name_constant;
     418:	48 8b 45 18 	movq	24(%rbp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:380
; }
     41c:	5d 	popq	%rbp
     41d:	c3 	retq

___proj__Mkstruct_fixed_header_constant__item__flags_constant:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:386
; {
     41e:	55 	pushq	%rbp
     41f:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:387
; return projectee.flags_constant;
     422:	8b 45 20 	movl	32(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:388
; }
     425:	5d 	popq	%rbp
     426:	c3 	retq

___proj__Mkstruct_variable_header_publish__item__topic_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:394
; {
     427:	55 	pushq	%rbp
     428:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:395
; return projectee.topic_length;
     42b:	8b 45 10 	movl	16(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:396
; }
     42e:	5d 	popq	%rbp
     42f:	c3 	retq

___proj__Mkstruct_variable_header_publish__item__topic_name:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:402
; {
     430:	55 	pushq	%rbp
     431:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:403
; return projectee.topic_name;
     434:	48 8b 45 18 	movq	24(%rbp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:404
; }
     438:	5d 	popq	%rbp
     439:	c3 	retq

___proj__Mkstruct_variable_header_publish__item__property_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:410
; {
     43a:	55 	pushq	%rbp
     43b:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:411
; return projectee.property_length;
     43e:	8b 45 20 	movl	32(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:412
; }
     441:	5d 	popq	%rbp
     442:	c3 	retq

___proj__Mkstruct_variable_header_publish__item__payload:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:418
; {
     443:	55 	pushq	%rbp
     444:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:419
; return projectee.payload;
     447:	48 8b 45 28 	movq	40(%rbp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:420
; }
     44b:	5d 	popq	%rbp
     44c:	c3 	retq

___proj__Mkstruct_error_struct__item__code:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:423
; {
     44d:	55 	pushq	%rbp
     44e:	48 89 e5 	movq	%rsp, %rbp
     451:	89 f8 	movl	%edi, %eax
     453:	48 89 f1 	movq	%rsi, %rcx
     456:	48 89 ca 	movq	%rcx, %rdx
     459:	48 89 45 f0 	movq	%rax, -16(%rbp)
     45d:	48 89 55 f8 	movq	%rdx, -8(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:424
; return projectee.code;
     461:	0f b6 45 f0 	movzbl	-16(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:425
; }
     465:	5d 	popq	%rbp
     466:	c3 	retq

___proj__Mkstruct_error_struct__item__message:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:428
; {
     467:	55 	pushq	%rbp
     468:	48 89 e5 	movq	%rsp, %rbp
     46b:	89 f8 	movl	%edi, %eax
     46d:	48 89 f1 	movq	%rsi, %rcx
     470:	48 89 ca 	movq	%rcx, %rdx
     473:	48 89 45 f0 	movq	%rax, -16(%rbp)
     477:	48 89 55 f8 	movq	%rdx, -8(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:429
; return projectee.message;
     47b:	48 8b 45 f8 	movq	-8(%rbp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:430
; }
     47f:	5d 	popq	%rbp
     480:	c3 	retq

___proj__Mkstruct_fixed_header__item__message_type:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:433
; {
     481:	55 	pushq	%rbp
     482:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:434
; return projectee.message_type;
     485:	0f b6 45 10 	movzbl	16(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:435
; }
     489:	5d 	popq	%rbp
     48a:	c3 	retq

___proj__Mkstruct_fixed_header__item__message_name:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:438
; {
     48b:	55 	pushq	%rbp
     48c:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:439
; return projectee.message_name;
     48f:	48 8b 45 18 	movq	24(%rbp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:440
; }
     493:	5d 	popq	%rbp
     494:	c3 	retq

___proj__Mkstruct_fixed_header__item__flags:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:443
; {
     495:	55 	pushq	%rbp
     496:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:444
; return projectee.flags;
     499:	8b 45 20 	movl	32(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:445
; }
     49c:	5d 	popq	%rbp
     49d:	c3 	retq

___proj__Mkstruct_fixed_header__item__remaining_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:448
; {
     49e:	55 	pushq	%rbp
     49f:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:449
; return projectee.remaining_length;
     4a2:	8b 45 24 	movl	36(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:450
; }
     4a5:	5d 	popq	%rbp
     4a6:	c3 	retq

___proj__Mkstruct_fixed_header__item__publish:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:454
; {
     4a7:	55 	pushq	%rbp
     4a8:	48 89 e5 	movq	%rsp, %rbp
     4ab:	48 89 7d f8 	movq	%rdi, -8(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:455
; return projectee.publish;
     4af:	48 8b 45 f8 	movq	-8(%rbp), %rax
     4b3:	48 8b 55 28 	movq	40(%rbp), %rdx
     4b7:	48 89 10 	movq	%rdx, (%rax)
     4ba:	48 8b 55 30 	movq	48(%rbp), %rdx
     4be:	48 89 50 08 	movq	%rdx, 8(%rax)
     4c2:	48 8b 55 38 	movq	56(%rbp), %rdx
     4c6:	48 89 50 10 	movq	%rdx, 16(%rax)
     4ca:	48 8b 55 40 	movq	64(%rbp), %rdx
     4ce:	48 89 50 18 	movq	%rdx, 24(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:456
; }
     4d2:	48 8b 45 f8 	movq	-8(%rbp), %rax
     4d6:	5d 	popq	%rbp
     4d7:	c3 	retq

___proj__Mkstruct_fixed_header__item__error:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:459
; {
     4d8:	55 	pushq	%rbp
     4d9:	48 89 e5 	movq	%rsp, %rbp
     4dc:	53 	pushq	%rbx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:460
; return projectee.error;
     4dd:	48 8b 45 48 	movq	72(%rbp), %rax
     4e1:	48 8b 55 50 	movq	80(%rbp), %rdx
     4e5:	48 89 c1 	movq	%rax, %rcx
     4e8:	48 89 d3 	movq	%rdx, %rbx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:461
; }
     4eb:	89 c8 	movl	%ecx, %eax
     4ed:	5b 	popq	%rbx
     4ee:	5d 	popq	%rbp
     4ef:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item___fixed_header_first_one_byte:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:467
; {
     4f0:	55 	pushq	%rbp
     4f1:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:468
; return projectee._fixed_header_first_one_byte;
     4f4:	0f b6 45 10 	movzbl	16(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:469
; }
     4f8:	5d 	popq	%rbp
     4f9:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item__is_searching_remaining_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:475
; {
     4fa:	55 	pushq	%rbp
     4fb:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:476
; return projectee.is_searching_remaining_length;
     4fe:	0f b6 45 11 	movzbl	17(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:477
; }
     502:	5d 	popq	%rbp
     503:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item__is_searching_property_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:483
; {
     504:	55 	pushq	%rbp
     505:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:484
; return projectee.is_searching_property_length;
     508:	0f b6 45 12 	movzbl	18(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:485
; }
     50c:	5d 	popq	%rbp
     50d:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item___message_type:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:489
; {
     50e:	55 	pushq	%rbp
     50f:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:490
; return projectee._message_type;
     512:	0f b6 45 13 	movzbl	19(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:491
; }
     516:	5d 	popq	%rbp
     517:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item___remaining_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:497
; {
     518:	55 	pushq	%rbp
     519:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:498
; return projectee._remaining_length;
     51c:	8b 45 14 	movl	20(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:499
; }
     51f:	5d 	popq	%rbp
     520:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item___topic_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:503
; {
     521:	55 	pushq	%rbp
     522:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:504
; return projectee._topic_length;
     525:	8b 45 18 	movl	24(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:505
; }
     528:	5d 	popq	%rbp
     529:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item___topic_name:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:509
; {
     52a:	55 	pushq	%rbp
     52b:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:510
; return projectee._topic_name;
     52e:	48 8b 45 20 	movq	32(%rbp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:511
; }
     532:	5d 	popq	%rbp
     533:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item___topic_name_error_status:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:517
; {
     534:	55 	pushq	%rbp
     535:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:518
; return projectee._topic_name_error_status;
     538:	0f b6 45 28 	movzbl	40(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:519
; }
     53c:	5d 	popq	%rbp
     53d:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item___property_length:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:525
; {
     53e:	55 	pushq	%rbp
     53f:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:526
; return projectee._property_length;
     542:	8b 45 2c 	movl	44(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:527
; }
     545:	5d 	popq	%rbp
     546:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item___payload:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:531
; {
     547:	55 	pushq	%rbp
     548:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:532
; return projectee._payload;
     54b:	48 8b 45 30 	movq	48(%rbp), %rax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:533
; }
     54f:	5d 	popq	%rbp
     550:	c3 	retq

___proj__Mkstruct_fixed_header_parts__item___payload_error_status:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:539
; {
     551:	55 	pushq	%rbp
     552:	48 89 e5 	movq	%rsp, %rbp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:540
; return projectee._payload_error_status;
     555:	0f b6 45 38 	movzbl	56(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:541
; }
     559:	5d 	popq	%rbp
     55a:	c3 	retq

_is_valid_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:544
; {
     55b:	55 	pushq	%rbp
     55c:	48 89 e5 	movq	%rsp, %rbp
     55f:	89 f8 	movl	%edi, %eax
     561:	88 45 fc 	movb	%al, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:545
; return s.flags_constant.flag == flag;
     564:	0f b6 45 20 	movzbl	32(%rbp), %eax
     568:	38 45 fc 	cmpb	%al, -4(%rbp)
     56b:	0f 94 c0 	sete	%al
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:546
; }
     56e:	5d 	popq	%rbp
     56f:	c3 	retq

_struct_fixed_publish:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:550
; {
     570:	55 	pushq	%rbp
     571:	48 89 e5 	movq	%rsp, %rbp
     574:	48 89 7d d8 	movq	%rdi, -40(%rbp)
     578:	89 c8 	movl	%ecx, %eax
     57a:	89 f1 	movl	%esi, %ecx
     57c:	88 4d d4 	movb	%cl, -44(%rbp)
     57f:	88 55 d0 	movb	%dl, -48(%rbp)
     582:	88 45 cc 	movb	%al, -52(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:552
; (
     585:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     58c:	48 8b 0d 00 00 00 00 	movq	(%rip), %rcx
     593:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     59a:	48 8b 75 d8 	movq	-40(%rbp), %rsi
     59e:	88 16 	movb	%dl, (%rsi)
     5a0:	48 8b 55 d8 	movq	-40(%rbp), %rdx
     5a4:	48 89 4a 08 	movq	%rcx, 8(%rdx)
     5a8:	48 8b 55 d8 	movq	-40(%rbp), %rdx
     5ac:	88 42 10 	movb	%al, 16(%rdx)
     5af:	48 8b 55 d8 	movq	-40(%rbp), %rdx
     5b3:	0f b6 45 d4 	movzbl	-44(%rbp), %eax
     5b7:	88 42 11 	movb	%al, 17(%rdx)
     5ba:	48 8b 55 d8 	movq	-40(%rbp), %rdx
     5be:	0f b6 45 d0 	movzbl	-48(%rbp), %eax
     5c2:	88 42 12 	movb	%al, 18(%rdx)
     5c5:	48 8b 55 d8 	movq	-40(%rbp), %rdx
     5c9:	0f b6 45 cc 	movzbl	-52(%rbp), %eax
     5cd:	88 42 13 	movb	%al, 19(%rdx)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:564
; }
     5d0:	48 8b 45 d8 	movq	-40(%rbp), %rax
     5d4:	5d 	popq	%rbp
     5d5:	c3 	retq

_get_struct_fixed_header_constant_except_publish:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:568
; {
     5d6:	55 	pushq	%rbp
     5d7:	48 89 e5 	movq	%rsp, %rbp
     5da:	48 81 ec 58 01 00 00 	subq	$344, %rsp
     5e1:	48 89 bd 38 fe ff ff 	movq	%rdi, -456(%rbp)
     5e8:	89 f0 	movl	%esi, %eax
     5ea:	88 85 34 fe ff ff 	movb	%al, -460(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:569
; if (message_type == define_mqtt_control_packet_CONNECT)
     5f0:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     5f7:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     5fd:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x96>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:571
; (
     5ff:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     606:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     60d:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     614:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     61b:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     622:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     629:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     630:	41 88 39 	movb	%dil, (%r9)
     633:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     63a:	4c 89 47 08 	movq	%r8, 8(%rdi)
     63e:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     645:	40 88 77 10 	movb	%sil, 16(%rdi)
     649:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     650:	88 4e 11 	movb	%cl, 17(%rsi)
     653:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     65a:	88 51 12 	movb	%dl, 18(%rcx)
     65d:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     664:	88 42 13 	movb	%al, 19(%rdx)
     667:	e9 35 06 00 00 	jmp	1589 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:583
; else if (message_type == define_mqtt_control_packet_CONNACK)
     66c:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     673:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     679:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x112>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:585
; (
     67b:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     682:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     689:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     690:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     697:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     69e:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     6a5:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     6ac:	41 88 39 	movb	%dil, (%r9)
     6af:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     6b6:	4c 89 47 08 	movq	%r8, 8(%rdi)
     6ba:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     6c1:	40 88 77 10 	movb	%sil, 16(%rdi)
     6c5:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     6cc:	88 4e 11 	movb	%cl, 17(%rsi)
     6cf:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     6d6:	88 51 12 	movb	%dl, 18(%rcx)
     6d9:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     6e0:	88 42 13 	movb	%al, 19(%rdx)
     6e3:	e9 b9 05 00 00 	jmp	1465 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:597
; else if (message_type == define_mqtt_control_packet_PUBACK)
     6e8:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     6ef:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     6f5:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x18e>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:599
; (
     6f7:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     6fe:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     705:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     70c:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     713:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     71a:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     721:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     728:	41 88 39 	movb	%dil, (%r9)
     72b:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     732:	4c 89 47 08 	movq	%r8, 8(%rdi)
     736:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     73d:	40 88 77 10 	movb	%sil, 16(%rdi)
     741:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     748:	88 4e 11 	movb	%cl, 17(%rsi)
     74b:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     752:	88 51 12 	movb	%dl, 18(%rcx)
     755:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     75c:	88 42 13 	movb	%al, 19(%rdx)
     75f:	e9 3d 05 00 00 	jmp	1341 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:611
; else if (message_type == define_mqtt_control_packet_PUBREC)
     764:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     76b:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     771:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x20a>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:613
; (
     773:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     77a:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     781:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     788:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     78f:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     796:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     79d:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     7a4:	41 88 39 	movb	%dil, (%r9)
     7a7:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     7ae:	4c 89 47 08 	movq	%r8, 8(%rdi)
     7b2:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     7b9:	40 88 77 10 	movb	%sil, 16(%rdi)
     7bd:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     7c4:	88 4e 11 	movb	%cl, 17(%rsi)
     7c7:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     7ce:	88 51 12 	movb	%dl, 18(%rcx)
     7d1:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     7d8:	88 42 13 	movb	%al, 19(%rdx)
     7db:	e9 c1 04 00 00 	jmp	1217 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:625
; else if (message_type == define_mqtt_control_packet_PUBREL)
     7e0:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     7e7:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     7ed:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x286>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:627
; (
     7ef:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     7f6:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     7fd:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     804:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     80b:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     812:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     819:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     820:	41 88 39 	movb	%dil, (%r9)
     823:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     82a:	4c 89 47 08 	movq	%r8, 8(%rdi)
     82e:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     835:	40 88 77 10 	movb	%sil, 16(%rdi)
     839:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     840:	88 4e 11 	movb	%cl, 17(%rsi)
     843:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     84a:	88 51 12 	movb	%dl, 18(%rcx)
     84d:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     854:	88 42 13 	movb	%al, 19(%rdx)
     857:	e9 45 04 00 00 	jmp	1093 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:639
; else if (message_type == define_mqtt_control_packet_PUBCOMP)
     85c:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     863:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     869:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x302>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:641
; (
     86b:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     872:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     879:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     880:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     887:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     88e:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     895:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     89c:	41 88 39 	movb	%dil, (%r9)
     89f:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     8a6:	4c 89 47 08 	movq	%r8, 8(%rdi)
     8aa:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     8b1:	40 88 77 10 	movb	%sil, 16(%rdi)
     8b5:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     8bc:	88 4e 11 	movb	%cl, 17(%rsi)
     8bf:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     8c6:	88 51 12 	movb	%dl, 18(%rcx)
     8c9:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     8d0:	88 42 13 	movb	%al, 19(%rdx)
     8d3:	e9 c9 03 00 00 	jmp	969 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:653
; else if (message_type == define_mqtt_control_packet_SUBSCRIBE)
     8d8:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     8df:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     8e5:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x37e>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:655
; (
     8e7:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     8ee:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     8f5:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     8fc:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     903:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     90a:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     911:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     918:	41 88 39 	movb	%dil, (%r9)
     91b:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     922:	4c 89 47 08 	movq	%r8, 8(%rdi)
     926:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     92d:	40 88 77 10 	movb	%sil, 16(%rdi)
     931:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     938:	88 4e 11 	movb	%cl, 17(%rsi)
     93b:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     942:	88 51 12 	movb	%dl, 18(%rcx)
     945:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     94c:	88 42 13 	movb	%al, 19(%rdx)
     94f:	e9 4d 03 00 00 	jmp	845 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:667
; else if (message_type == define_mqtt_control_packet_SUBACK)
     954:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     95b:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     961:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x3fa>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:669
; (
     963:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     96a:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     971:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     978:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     97f:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     986:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     98d:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     994:	41 88 39 	movb	%dil, (%r9)
     997:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     99e:	4c 89 47 08 	movq	%r8, 8(%rdi)
     9a2:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     9a9:	40 88 77 10 	movb	%sil, 16(%rdi)
     9ad:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     9b4:	88 4e 11 	movb	%cl, 17(%rsi)
     9b7:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     9be:	88 51 12 	movb	%dl, 18(%rcx)
     9c1:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     9c8:	88 42 13 	movb	%al, 19(%rdx)
     9cb:	e9 d1 02 00 00 	jmp	721 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:681
; else if (message_type == define_mqtt_control_packet_UNSUBSCRIBE)
     9d0:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     9d7:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     9dd:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x476>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:683
; (
     9df:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     9e6:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     9ed:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     9f4:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     9fb:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     a02:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     a09:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     a10:	41 88 39 	movb	%dil, (%r9)
     a13:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     a1a:	4c 89 47 08 	movq	%r8, 8(%rdi)
     a1e:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     a25:	40 88 77 10 	movb	%sil, 16(%rdi)
     a29:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     a30:	88 4e 11 	movb	%cl, 17(%rsi)
     a33:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     a3a:	88 51 12 	movb	%dl, 18(%rcx)
     a3d:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     a44:	88 42 13 	movb	%al, 19(%rdx)
     a47:	e9 55 02 00 00 	jmp	597 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:695
; else if (message_type == define_mqtt_control_packet_UNSUBACK)
     a4c:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     a53:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     a59:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x4f2>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:697
; (
     a5b:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     a62:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     a69:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     a70:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     a77:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     a7e:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     a85:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     a8c:	41 88 39 	movb	%dil, (%r9)
     a8f:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     a96:	4c 89 47 08 	movq	%r8, 8(%rdi)
     a9a:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     aa1:	40 88 77 10 	movb	%sil, 16(%rdi)
     aa5:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     aac:	88 4e 11 	movb	%cl, 17(%rsi)
     aaf:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     ab6:	88 51 12 	movb	%dl, 18(%rcx)
     ab9:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     ac0:	88 42 13 	movb	%al, 19(%rdx)
     ac3:	e9 d9 01 00 00 	jmp	473 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:709
; else if (message_type == define_mqtt_control_packet_PINGREQ)
     ac8:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     acf:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     ad5:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x56e>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:711
; (
     ad7:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     ade:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     ae5:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     aec:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     af3:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     afa:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     b01:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     b08:	41 88 39 	movb	%dil, (%r9)
     b0b:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     b12:	4c 89 47 08 	movq	%r8, 8(%rdi)
     b16:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     b1d:	40 88 77 10 	movb	%sil, 16(%rdi)
     b21:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     b28:	88 4e 11 	movb	%cl, 17(%rsi)
     b2b:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     b32:	88 51 12 	movb	%dl, 18(%rcx)
     b35:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     b3c:	88 42 13 	movb	%al, 19(%rdx)
     b3f:	e9 5d 01 00 00 	jmp	349 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:723
; else if (message_type == define_mqtt_control_packet_PINGRESP)
     b44:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     b4b:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     b51:	75 6d 	jne	109 <_get_struct_fixed_header_constant_except_publish+0x5ea>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:725
; (
     b53:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     b5a:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     b61:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     b68:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     b6f:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     b76:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     b7d:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     b84:	41 88 39 	movb	%dil, (%r9)
     b87:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     b8e:	4c 89 47 08 	movq	%r8, 8(%rdi)
     b92:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     b99:	40 88 77 10 	movb	%sil, 16(%rdi)
     b9d:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     ba4:	88 4e 11 	movb	%cl, 17(%rsi)
     ba7:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     bae:	88 51 12 	movb	%dl, 18(%rcx)
     bb1:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     bb8:	88 42 13 	movb	%al, 19(%rdx)
     bbb:	e9 e1 00 00 00 	jmp	225 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:737
; else if (message_type == define_mqtt_control_packet_DISCONNECT)
     bc0:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     bc7:	38 85 34 fe ff ff 	cmpb	%al, -460(%rbp)
     bcd:	75 6a 	jne	106 <_get_struct_fixed_header_constant_except_publish+0x663>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:739
; (
     bcf:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     bd6:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     bdd:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     be4:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     beb:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     bf2:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     bf9:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     c00:	41 88 39 	movb	%dil, (%r9)
     c03:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     c0a:	4c 89 47 08 	movq	%r8, 8(%rdi)
     c0e:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     c15:	40 88 77 10 	movb	%sil, 16(%rdi)
     c19:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     c20:	88 4e 11 	movb	%cl, 17(%rsi)
     c23:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     c2a:	88 51 12 	movb	%dl, 18(%rcx)
     c2d:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     c34:	88 42 13 	movb	%al, 19(%rdx)
     c37:	eb 68 	jmp	104 <_get_struct_fixed_header_constant_except_publish+0x6cb>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:753
; (
     c39:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     c40:	4c 8b 05 00 00 00 00 	movq	(%rip), %r8
     c47:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     c4e:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     c55:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     c5c:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     c63:	4c 8b 8d 38 fe ff ff 	movq	-456(%rbp), %r9
     c6a:	41 88 39 	movb	%dil, (%r9)
     c6d:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     c74:	4c 89 47 08 	movq	%r8, 8(%rdi)
     c78:	48 8b bd 38 fe ff ff 	movq	-456(%rbp), %rdi
     c7f:	40 88 77 10 	movb	%sil, 16(%rdi)
     c83:	48 8b b5 38 fe ff ff 	movq	-456(%rbp), %rsi
     c8a:	88 4e 11 	movb	%cl, 17(%rsi)
     c8d:	48 8b 8d 38 fe ff ff 	movq	-456(%rbp), %rcx
     c94:	88 51 12 	movb	%dl, 18(%rcx)
     c97:	48 8b 95 38 fe ff ff 	movq	-456(%rbp), %rdx
     c9e:	88 42 13 	movb	%al, 19(%rdx)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:765
; }
     ca1:	48 8b 85 38 fe ff ff 	movq	-456(%rbp), %rax
     ca8:	c9 	leave
     ca9:	c3 	retq

_error_struct_fixed_header:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:768
; {
     caa:	55 	pushq	%rbp
     cab:	48 89 e5 	movq	%rsp, %rbp
     cae:	48 89 7d a8 	movq	%rdi, -88(%rbp)
     cb2:	48 89 d1 	movq	%rdx, %rcx
     cb5:	48 89 f0 	movq	%rsi, %rax
     cb8:	48 89 fa 	movq	%rdi, %rdx
     cbb:	48 89 ca 	movq	%rcx, %rdx
     cbe:	48 89 45 90 	movq	%rax, -112(%rbp)
     cc2:	48 89 55 98 	movq	%rdx, -104(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:770
; (
     cc6:	0f b6 3d 00 00 00 00 	movzbl	(%rip), %edi
     ccd:	0f b6 35 00 00 00 00 	movzbl	(%rip), %esi
     cd4:	0f b6 0d 00 00 00 00 	movzbl	(%rip), %ecx
     cdb:	0f b6 15 00 00 00 00 	movzbl	(%rip), %edx
     ce2:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     ce9:	44 8b 15 00 00 00 00 	movl	(%rip), %r10d
     cf0:	44 8b 0d 00 00 00 00 	movl	(%rip), %r9d
     cf7:	44 8b 05 00 00 00 00 	movl	(%rip), %r8d
     cfe:	4c 8b 5d a8 	movq	-88(%rbp), %r11
     d02:	41 88 3b 	movb	%dil, (%r11)
     d05:	48 8b 7d a8 	movq	-88(%rbp), %rdi
     d09:	4c 8d 1d 00 00 00 00 	leaq	(%rip), %r11
     d10:	4c 89 5f 08 	movq	%r11, 8(%rdi)
     d14:	48 8b 7d a8 	movq	-88(%rbp), %rdi
     d18:	40 88 77 10 	movb	%sil, 16(%rdi)
     d1c:	48 8b 75 a8 	movq	-88(%rbp), %rsi
     d20:	88 4e 11 	movb	%cl, 17(%rsi)
     d23:	48 8b 4d a8 	movq	-88(%rbp), %rcx
     d27:	88 51 12 	movb	%dl, 18(%rcx)
     d2a:	48 8b 55 a8 	movq	-88(%rbp), %rdx
     d2e:	88 42 13 	movb	%al, 19(%rdx)
     d31:	48 8b 45 a8 	movq	-88(%rbp), %rax
     d35:	44 89 50 14 	movl	%r10d, 20(%rax)
     d39:	48 8b 45 a8 	movq	-88(%rbp), %rax
     d3d:	44 89 48 18 	movl	%r9d, 24(%rax)
     d41:	48 8b 45 a8 	movq	-88(%rbp), %rax
     d45:	48 8d 15 00 00 00 00 	leaq	(%rip), %rdx
     d4c:	48 89 50 20 	movq	%rdx, 32(%rax)
     d50:	48 8b 45 a8 	movq	-88(%rbp), %rax
     d54:	44 89 40 28 	movl	%r8d, 40(%rax)
     d58:	48 8b 45 a8 	movq	-88(%rbp), %rax
     d5c:	48 8d 15 00 00 00 00 	leaq	(%rip), %rdx
     d63:	48 89 50 30 	movq	%rdx, 48(%rax)
     d67:	48 8b 4d a8 	movq	-88(%rbp), %rcx
     d6b:	48 8b 45 90 	movq	-112(%rbp), %rax
     d6f:	48 8b 55 98 	movq	-104(%rbp), %rdx
     d73:	48 89 41 38 	movq	%rax, 56(%rcx)
     d77:	48 89 51 40 	movq	%rdx, 64(%rcx)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:785
; }
     d7b:	48 8b 45 a8 	movq	-88(%rbp), %rax
     d7f:	5d 	popq	%rbp
     d80:	c3 	retq

_get_dup_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:788
; {
     d81:	55 	pushq	%rbp
     d82:	48 89 e5 	movq	%rsp, %rbp
     d85:	48 83 8c 24 e0 ef ff ff 00 	orq	$0, -4128(%rsp)
     d8e:	48 83 ec 20 	subq	$32, %rsp
     d92:	89 f8 	movl	%edi, %eax
     d94:	88 45 ec 	movb	%al, -20(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:789
; uint8_t dup_flag_bits = slice_byte(fixed_header_first_one_byte, (uint8_t)4U, (uint8_t)5U);
     d97:	0f b6 45 ec 	movzbl	-20(%rbp), %eax
     d9b:	ba 05 00 00 00 	movl	$5, %edx
     da0:	be 04 00 00 00 	movl	$4, %esi
     da5:	89 c7 	movl	%eax, %edi
     da7:	e8 00 00 00 00 	callq	0 <_get_dup_flag+0x2b>
     dac:	88 45 ff 	movb	%al, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:790
; if (dup_flag_bits > (uint8_t)1U)
     daf:	80 7d ff 01 	cmpb	$1, -1(%rbp)
     db3:	76 09 	jbe	9 <_get_dup_flag+0x3d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:791
; return max_u8;
     db5:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     dbc:	eb 04 	jmp	4 <_get_dup_flag+0x41>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:793
; return dup_flag_bits;
     dbe:	0f b6 45 ff 	movzbl	-1(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:794
; }
     dc2:	c9 	leave
     dc3:	c3 	retq

_get_qos_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:797
; {
     dc4:	55 	pushq	%rbp
     dc5:	48 89 e5 	movq	%rsp, %rbp
     dc8:	48 83 8c 24 e0 ef ff ff 00 	orq	$0, -4128(%rsp)
     dd1:	48 83 ec 20 	subq	$32, %rsp
     dd5:	89 f8 	movl	%edi, %eax
     dd7:	88 45 ec 	movb	%al, -20(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:798
; uint8_t qos_flag_bits = slice_byte(fixed_header_first_one_byte, (uint8_t)5U, (uint8_t)7U);
     dda:	0f b6 45 ec 	movzbl	-20(%rbp), %eax
     dde:	ba 07 00 00 00 	movl	$7, %edx
     de3:	be 05 00 00 00 	movl	$5, %esi
     de8:	89 c7 	movl	%eax, %edi
     dea:	e8 00 00 00 00 	callq	0 <_get_qos_flag+0x2b>
     def:	88 45 ff 	movb	%al, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:799
; if (qos_flag_bits > (uint8_t)2U)
     df2:	80 7d ff 02 	cmpb	$2, -1(%rbp)
     df6:	76 09 	jbe	9 <_get_qos_flag+0x3d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:800
; return max_u8;
     df8:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     dff:	eb 04 	jmp	4 <_get_qos_flag+0x41>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:802
; return qos_flag_bits;
     e01:	0f b6 45 ff 	movzbl	-1(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:803
; }
     e05:	c9 	leave
     e06:	c3 	retq

_get_retain_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:806
; {
     e07:	55 	pushq	%rbp
     e08:	48 89 e5 	movq	%rsp, %rbp
     e0b:	48 83 8c 24 e0 ef ff ff 00 	orq	$0, -4128(%rsp)
     e14:	48 83 ec 20 	subq	$32, %rsp
     e18:	89 f8 	movl	%edi, %eax
     e1a:	88 45 ec 	movb	%al, -20(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:807
; uint8_t retain_flag_bits = slice_byte(fixed_header_first_one_byte, (uint8_t)7U, (uint8_t)8U);
     e1d:	0f b6 45 ec 	movzbl	-20(%rbp), %eax
     e21:	ba 08 00 00 00 	movl	$8, %edx
     e26:	be 07 00 00 00 	movl	$7, %esi
     e2b:	89 c7 	movl	%eax, %edi
     e2d:	e8 00 00 00 00 	callq	0 <_get_retain_flag+0x2b>
     e32:	88 45 ff 	movb	%al, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:808
; if (retain_flag_bits > (uint8_t)1U)
     e35:	80 7d ff 01 	cmpb	$1, -1(%rbp)
     e39:	76 09 	jbe	9 <_get_retain_flag+0x3d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:809
; return max_u8;
     e3b:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     e42:	eb 04 	jmp	4 <_get_retain_flag+0x41>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:811
; return retain_flag_bits;
     e44:	0f b6 45 ff 	movzbl	-1(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:812
; }
     e48:	c9 	leave
     e49:	c3 	retq

_get_flag:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:815
; {
     e4a:	55 	pushq	%rbp
     e4b:	48 89 e5 	movq	%rsp, %rbp
     e4e:	48 83 8c 24 e0 ef ff ff 00 	orq	$0, -4128(%rsp)
     e57:	48 83 ec 20 	subq	$32, %rsp
     e5b:	89 fa 	movl	%edi, %edx
     e5d:	89 f0 	movl	%esi, %eax
     e5f:	88 55 ec 	movb	%dl, -20(%rbp)
     e62:	88 45 e8 	movb	%al, -24(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:816
; uint8_t v1 = slice_byte(fixed_header_first_one_byte, (uint8_t)4U, (uint8_t)8U);
     e65:	0f b6 45 e8 	movzbl	-24(%rbp), %eax
     e69:	ba 08 00 00 00 	movl	$8, %edx
     e6e:	be 04 00 00 00 	movl	$4, %esi
     e73:	89 c7 	movl	%eax, %edi
     e75:	e8 00 00 00 00 	callq	0 <_get_flag+0x30>
     e7a:	88 45 ff 	movb	%al, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:820
; == define_mqtt_control_packet_PUBREL
     e7d:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:818
; (
     e84:	38 45 ec 	cmpb	%al, -20(%rbp)
     e87:	74 18 	je	24 <_get_flag+0x57>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:821
; || message_type == define_mqtt_control_packet_SUBSCRIBE
     e89:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     e90:	38 45 ec 	cmpb	%al, -20(%rbp)
     e93:	74 0c 	je	12 <_get_flag+0x57>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:822
; || message_type == define_mqtt_control_packet_UNSUBSCRIBE
     e95:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     e9c:	38 45 ec 	cmpb	%al, -20(%rbp)
     e9f:	75 15 	jne	21 <_get_flag+0x6c>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:824
; if (v1 != (uint8_t)0b0010U)
     ea1:	80 7d ff 02 	cmpb	$2, -1(%rbp)
     ea5:	74 09 	je	9 <_get_flag+0x66>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:825
; return max_u8;
     ea7:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     eae:	eb 19 	jmp	25 <_get_flag+0x7f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:827
; return v1;
     eb0:	0f b6 45 ff 	movzbl	-1(%rbp), %eax
     eb4:	eb 13 	jmp	19 <_get_flag+0x7f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:828
; else if (v1 != (uint8_t)0b0000U)
     eb6:	80 7d ff 00 	cmpb	$0, -1(%rbp)
     eba:	74 09 	je	9 <_get_flag+0x7b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:829
; return max_u8;
     ebc:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     ec3:	eb 04 	jmp	4 <_get_flag+0x7f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:831
; return v1;
     ec5:	0f b6 45 ff 	movzbl	-1(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:832
; }
     ec9:	c9 	leave
     eca:	c3 	retq

_get_fixed_header:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:835
; {
     ecb:	55 	pushq	%rbp
     ecc:	48 89 e5 	movq	%rsp, %rbp
     ecf:	41 56 	pushq	%r14
     ed1:	41 55 	pushq	%r13
     ed3:	41 54 	pushq	%r12
     ed5:	53 	pushq	%rbx
     ed6:	48 83 8c 24 30 ef ff ff 00 	orq	$0, -4304(%rsp)
     edf:	48 81 ec d0 00 00 00 	subq	$208, %rsp
     ee6:	48 89 bd 18 ff ff ff 	movq	%rdi, -232(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:836
; if (s._message_type == define_mqtt_control_packet_PUBLISH)
     eed:	0f b6 55 13 	movzbl	19(%rbp), %edx
     ef1:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     ef8:	38 c2 	cmpb	%al, %dl
     efa:	0f 85 de 02 00 00 	jne	734 <_get_fixed_header+0x313>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:838
; uint8_t dup_flag = get_dup_flag(s._fixed_header_first_one_byte);
     f00:	0f b6 45 10 	movzbl	16(%rbp), %eax
     f04:	0f b6 c0 	movzbl	%al, %eax
     f07:	89 c7 	movl	%eax, %edi
     f09:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0x43>
     f0e:	88 45 dd 	movb	%al, -35(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:839
; uint8_t qos_flag = get_qos_flag(s._fixed_header_first_one_byte);
     f11:	0f b6 45 10 	movzbl	16(%rbp), %eax
     f15:	0f b6 c0 	movzbl	%al, %eax
     f18:	89 c7 	movl	%eax, %edi
     f1a:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0x54>
     f1f:	88 45 dc 	movb	%al, -36(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:840
; uint8_t retain_flag = get_retain_flag(s._fixed_header_first_one_byte);
     f22:	0f b6 45 10 	movzbl	16(%rbp), %eax
     f26:	0f b6 c0 	movzbl	%al, %eax
     f29:	89 c7 	movl	%eax, %edi
     f2b:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0x65>
     f30:	88 45 db 	movb	%al, -37(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:843
; s.is_searching_remaining_length
     f33:	0f b6 45 11 	movzbl	17(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:851
; || s._payload_error_status > (uint8_t)0U;
     f37:	84 c0 	testb	%al, %al
     f39:	75 58 	jne	88 <_get_fixed_header+0xc8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:844
; || s._message_type == max_u8
     f3b:	0f b6 55 13 	movzbl	19(%rbp), %edx
     f3f:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     f46:	38 c2 	cmpb	%al, %dl
     f48:	74 49 	je	73 <_get_fixed_header+0xc8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:845
; || dup_flag == max_u8
     f4a:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     f51:	38 45 dd 	cmpb	%al, -35(%rbp)
     f54:	74 3d 	je	61 <_get_fixed_header+0xc8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:846
; || qos_flag == max_u8
     f56:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     f5d:	38 45 dc 	cmpb	%al, -36(%rbp)
     f60:	74 31 	je	49 <_get_fixed_header+0xc8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:847
; || retain_flag == max_u8
     f62:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     f69:	38 45 db 	cmpb	%al, -37(%rbp)
     f6c:	74 25 	je	37 <_get_fixed_header+0xc8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:848
; || s._topic_name_error_status > (uint8_t)0U
     f6e:	0f b6 45 28 	movzbl	40(%rbp), %eax
     f72:	84 c0 	testb	%al, %al
     f74:	75 1d 	jne	29 <_get_fixed_header+0xc8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:849
; || s._topic_length == max_u32
     f76:	8b 55 18 	movl	24(%rbp), %edx
     f79:	8b 05 00 00 00 00 	movl	(%rip), %eax
     f7f:	39 c2 	cmpl	%eax, %edx
     f81:	74 10 	je	16 <_get_fixed_header+0xc8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:850
; || s.is_searching_property_length
     f83:	0f b6 45 12 	movzbl	18(%rbp), %eax
     f87:	84 c0 	testb	%al, %al
     f89:	75 08 	jne	8 <_get_fixed_header+0xc8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:851
; || s._payload_error_status > (uint8_t)0U;
     f8b:	0f b6 45 38 	movzbl	56(%rbp), %eax
     f8f:	84 c0 	testb	%al, %al
     f91:	74 07 	je	7 <_get_fixed_header+0xcf>
     f93:	b8 01 00 00 00 	movl	$1, %eax
     f98:	eb 05 	jmp	5 <_get_fixed_header+0xd4>
     f9a:	b8 00 00 00 00 	movl	$0, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:842
; have_error =
     f9f:	88 45 da 	movb	%al, -38(%rbp)
     fa2:	80 65 da 01 	andb	$1, -38(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:852
; if (have_error)
     fa6:	80 7d da 00 	cmpb	$0, -38(%rbp)
     faa:	0f 84 4e 01 00 00 	je	334 <_get_fixed_header+0x233>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:855
; if (s.is_searching_remaining_length)
     fb0:	0f b6 45 11 	movzbl	17(%rbp), %eax
     fb4:	84 c0 	testb	%al, %al
     fb6:	74 1a 	je	26 <_get_fixed_header+0x107>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:856
; error_struct =
     fb8:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     fbf:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
     fc6:	88 45 c0 	movb	%al, -64(%rbp)
     fc9:	48 89 55 c8 	movq	%rdx, -56(%rbp)
     fcd:	e9 0f 01 00 00 	jmp	271 <_get_fixed_header+0x216>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:863
; else if (s._message_type == max_u8)
     fd2:	0f b6 55 13 	movzbl	19(%rbp), %edx
     fd6:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     fdd:	38 c2 	cmpb	%al, %dl
     fdf:	75 1a 	jne	26 <_get_fixed_header+0x130>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:864
; error_struct =
     fe1:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
     fe8:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
     fef:	88 45 c0 	movb	%al, -64(%rbp)
     ff2:	48 89 55 c8 	movq	%rdx, -56(%rbp)
     ff6:	e9 e6 00 00 00 	jmp	230 <_get_fixed_header+0x216>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:871
; else if (dup_flag == max_u8)
     ffb:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    1002:	38 45 dd 	cmpb	%al, -35(%rbp)
    1005:	75 1a 	jne	26 <_get_fixed_header+0x156>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:872
; error_struct =
    1007:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    100e:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    1015:	88 45 c0 	movb	%al, -64(%rbp)
    1018:	48 89 55 c8 	movq	%rdx, -56(%rbp)
    101c:	e9 c0 00 00 00 	jmp	192 <_get_fixed_header+0x216>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:879
; else if (qos_flag == max_u8)
    1021:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    1028:	38 45 dc 	cmpb	%al, -36(%rbp)
    102b:	75 1a 	jne	26 <_get_fixed_header+0x17c>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:880
; error_struct =
    102d:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    1034:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    103b:	88 45 c0 	movb	%al, -64(%rbp)
    103e:	48 89 55 c8 	movq	%rdx, -56(%rbp)
    1042:	e9 9a 00 00 00 	jmp	154 <_get_fixed_header+0x216>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:887
; else if (retain_flag == max_u8)
    1047:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    104e:	38 45 db 	cmpb	%al, -37(%rbp)
    1051:	75 17 	jne	23 <_get_fixed_header+0x19f>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:888
; error_struct =
    1053:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    105a:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    1061:	88 45 c0 	movb	%al, -64(%rbp)
    1064:	48 89 55 c8 	movq	%rdx, -56(%rbp)
    1068:	eb 77 	jmp	119 <_get_fixed_header+0x216>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:895
; else if (s._topic_length == max_u32)
    106a:	8b 55 18 	movl	24(%rbp), %edx
    106d:	8b 05 00 00 00 00 	movl	(%rip), %eax
    1073:	39 c2 	cmpl	%eax, %edx
    1075:	75 17 	jne	23 <_get_fixed_header+0x1c3>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:896
; error_struct =
    1077:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    107e:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    1085:	88 45 c0 	movb	%al, -64(%rbp)
    1088:	48 89 55 c8 	movq	%rdx, -56(%rbp)
    108c:	eb 53 	jmp	83 <_get_fixed_header+0x216>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:903
; else if (s._topic_name_error_status > (uint8_t)0U)
    108e:	0f b6 45 28 	movzbl	40(%rbp), %eax
    1092:	84 c0 	testb	%al, %al
    1094:	74 17 	je	23 <_get_fixed_header+0x1e2>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:904
; error_struct =
    1096:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    109d:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    10a4:	88 45 c0 	movb	%al, -64(%rbp)
    10a7:	48 89 55 c8 	movq	%rdx, -56(%rbp)
    10ab:	eb 34 	jmp	52 <_get_fixed_header+0x216>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:911
; else if (s.is_searching_property_length)
    10ad:	0f b6 45 12 	movzbl	18(%rbp), %eax
    10b1:	84 c0 	testb	%al, %al
    10b3:	74 17 	je	23 <_get_fixed_header+0x201>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:912
; error_struct =
    10b5:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    10bc:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    10c3:	88 45 c0 	movb	%al, -64(%rbp)
    10c6:	48 89 55 c8 	movq	%rdx, -56(%rbp)
    10ca:	eb 15 	jmp	21 <_get_fixed_header+0x216>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:920
; error_struct =
    10cc:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    10d3:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    10da:	88 45 c0 	movb	%al, -64(%rbp)
    10dd:	48 89 55 c8 	movq	%rdx, -56(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:927
; return error_struct_fixed_header(error_struct);
    10e1:	48 8b 85 18 ff ff ff 	movq	-232(%rbp), %rax
    10e8:	8b 4d c0 	movl	-64(%rbp), %ecx
    10eb:	48 8b 55 c8 	movq	-56(%rbp), %rdx
    10ef:	89 ce 	movl	%ecx, %esi
    10f1:	48 89 c7 	movq	%rax, %rdi
    10f4:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0x22e>
    10f9:	e9 c6 02 00 00 	jmp	710 <_get_fixed_header+0x4f9>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:931
; struct_fixed_header_constant data = struct_fixed_publish(dup_flag, qos_flag, retain_flag);
    10fe:	0f b6 4d db 	movzbl	-37(%rbp), %ecx
    1102:	0f b6 55 dc 	movzbl	-36(%rbp), %edx
    1106:	0f b6 75 dd 	movzbl	-35(%rbp), %esi
    110a:	48 8d 45 a0 	leaq	-96(%rbp), %rax
    110e:	48 89 c7 	movq	%rax, %rdi
    1111:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0x24b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:935
; .message_type = data.message_type_constant,
    1116:	44 0f b6 45 a0 	movzbl	-96(%rbp), %r8d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:936
; .message_name = data.message_name_constant,
    111b:	4c 8b 6d a8 	movq	-88(%rbp), %r13
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:938
; .flag = data.flags_constant.flag,
    111f:	0f b6 7d b0 	movzbl	-80(%rbp), %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:939
; .dup_flag = data.flags_constant.dup_flag,
    1123:	0f b6 75 b1 	movzbl	-79(%rbp), %esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:940
; .qos_flag = data.flags_constant.qos_flag,
    1127:	0f b6 4d b2 	movzbl	-78(%rbp), %ecx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:941
; .retain_flag = data.flags_constant.retain_flag
    112b:	0f b6 55 b3 	movzbl	-77(%rbp), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:943
; .remaining_length = s._remaining_length,
    112f:	44 8b 65 14 	movl	20(%rbp), %r12d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:945
; .topic_length = s._topic_length,
    1133:	8b 5d 18 	movl	24(%rbp), %ebx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:946
; .topic_name = s._topic_name,
    1136:	4c 8b 5d 20 	movq	32(%rbp), %r11
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:948
; .payload = s._payload
    113a:	4c 8b 55 30 	movq	48(%rbp), %r10
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:933
; (
    113e:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    1145:	4c 8b 0d 00 00 00 00 	movq	(%rip), %r9
    114c:	4c 8b b5 18 ff ff ff 	movq	-232(%rbp), %r14
    1153:	45 88 06 	movb	%r8b, (%r14)
    1156:	4c 8b 85 18 ff ff ff 	movq	-232(%rbp), %r8
    115d:	4d 89 68 08 	movq	%r13, 8(%r8)
    1161:	4c 8b 85 18 ff ff ff 	movq	-232(%rbp), %r8
    1168:	41 88 78 10 	movb	%dil, 16(%r8)
    116c:	48 8b bd 18 ff ff ff 	movq	-232(%rbp), %rdi
    1173:	40 88 77 11 	movb	%sil, 17(%rdi)
    1177:	48 8b b5 18 ff ff ff 	movq	-232(%rbp), %rsi
    117e:	88 4e 12 	movb	%cl, 18(%rsi)
    1181:	48 8b 8d 18 ff ff ff 	movq	-232(%rbp), %rcx
    1188:	88 51 13 	movb	%dl, 19(%rcx)
    118b:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    1192:	44 89 62 14 	movl	%r12d, 20(%rdx)
    1196:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    119d:	89 5a 18 	movl	%ebx, 24(%rdx)
    11a0:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    11a7:	4c 89 5a 20 	movq	%r11, 32(%rdx)
    11ab:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    11b2:	c7 42 28 00 00 00 00 	movl	$0, 40(%rdx)
    11b9:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    11c0:	4c 89 52 30 	movq	%r10, 48(%rdx)
    11c4:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    11cb:	88 42 38 	movb	%al, 56(%rdx)
    11ce:	48 8b 85 18 ff ff ff 	movq	-232(%rbp), %rax
    11d5:	4c 89 48 40 	movq	%r9, 64(%rax)
    11d9:	e9 e6 01 00 00 	jmp	486 <_get_fixed_header+0x4f9>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:957
; uint8_t flag = get_flag(s._message_type, s._fixed_header_first_one_byte);
    11de:	0f b6 45 10 	movzbl	16(%rbp), %eax
    11e2:	0f b6 d0 	movzbl	%al, %edx
    11e5:	0f b6 45 13 	movzbl	19(%rbp), %eax
    11e9:	0f b6 c0 	movzbl	%al, %eax
    11ec:	89 d6 	movl	%edx, %esi
    11ee:	89 c7 	movl	%eax, %edi
    11f0:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0x32a>
    11f5:	88 45 df 	movb	%al, -33(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:959
; data = get_struct_fixed_header_constant_except_publish(s._message_type);
    11f8:	0f b6 45 13 	movzbl	19(%rbp), %eax
    11fc:	0f b6 d0 	movzbl	%al, %edx
    11ff:	48 8d 45 80 	leaq	-128(%rbp), %rax
    1203:	89 d6 	movl	%edx, %esi
    1205:	48 89 c7 	movq	%rax, %rdi
    1208:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0x342>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:962
; s.is_searching_remaining_length
    120d:	0f b6 45 11 	movzbl	17(%rbp), %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:964
; || is_valid_flag(data, flag) == false;
    1211:	84 c0 	testb	%al, %al
    1213:	75 32 	jne	50 <_get_fixed_header+0x37c>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:963
; || s._message_type == max_u8
    1215:	0f b6 55 13 	movzbl	19(%rbp), %edx
    1219:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    1220:	38 c2 	cmpb	%al, %dl
    1222:	74 23 	je	35 <_get_fixed_header+0x37c>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:964
; || is_valid_flag(data, flag) == false;
    1224:	0f b6 45 df 	movzbl	-33(%rbp), %eax
    1228:	48 83 ec 08 	subq	$8, %rsp
    122c:	ff 75 90 	pushq	-112(%rbp)
    122f:	ff 75 88 	pushq	-120(%rbp)
    1232:	ff 75 80 	pushq	-128(%rbp)
    1235:	89 c7 	movl	%eax, %edi
    1237:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0x371>
    123c:	48 83 c4 20 	addq	$32, %rsp
    1240:	83 f0 01 	xorl	$1, %eax
    1243:	84 c0 	testb	%al, %al
    1245:	74 07 	je	7 <_get_fixed_header+0x383>
    1247:	b8 01 00 00 00 	movl	$1, %eax
    124c:	eb 05 	jmp	5 <_get_fixed_header+0x388>
    124e:	b8 00 00 00 00 	movl	$0, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:961
; have_error =
    1253:	88 45 de 	movb	%al, -34(%rbp)
    1256:	80 65 de 01 	andb	$1, -34(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:965
; if (have_error)
    125a:	80 7d de 00 	cmpb	$0, -34(%rbp)
    125e:	0f 84 8f 00 00 00 	je	143 <_get_fixed_header+0x428>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:968
; if (s.is_searching_remaining_length)
    1264:	0f b6 45 11 	movzbl	17(%rbp), %eax
    1268:	84 c0 	testb	%al, %al
    126a:	74 1d 	je	29 <_get_fixed_header+0x3be>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:969
; error_struct =
    126c:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    1273:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    127a:	88 85 70 ff ff ff 	movb	%al, -144(%rbp)
    1280:	48 89 95 78 ff ff ff 	movq	%rdx, -136(%rbp)
    1287:	eb 47 	jmp	71 <_get_fixed_header+0x405>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:976
; else if (s._message_type == max_u8)
    1289:	0f b6 55 13 	movzbl	19(%rbp), %edx
    128d:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    1294:	38 c2 	cmpb	%al, %dl
    1296:	75 1d 	jne	29 <_get_fixed_header+0x3ea>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:977
; error_struct =
    1298:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    129f:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    12a6:	88 85 70 ff ff ff 	movb	%al, -144(%rbp)
    12ac:	48 89 95 78 ff ff ff 	movq	%rdx, -136(%rbp)
    12b3:	eb 1b 	jmp	27 <_get_fixed_header+0x405>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:985
; error_struct =
    12b5:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    12bc:	48 8b 15 00 00 00 00 	movq	(%rip), %rdx
    12c3:	88 85 70 ff ff ff 	movb	%al, -144(%rbp)
    12c9:	48 89 95 78 ff ff ff 	movq	%rdx, -136(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:992
; return error_struct_fixed_header(error_struct);
    12d0:	48 8b 85 18 ff ff ff 	movq	-232(%rbp), %rax
    12d7:	8b 8d 70 ff ff ff 	movl	-144(%rbp), %ecx
    12dd:	48 8b 95 78 ff ff ff 	movq	-136(%rbp), %rdx
    12e4:	89 ce 	movl	%ecx, %esi
    12e6:	48 89 c7 	movq	%rax, %rdi
    12e9:	e8 00 00 00 00 	callq	0 <_get_fixed_header+0x423>
    12ee:	e9 d1 00 00 00 	jmp	209 <_get_fixed_header+0x4f9>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:998
; .message_type = data.message_type_constant,
    12f3:	44 0f b6 45 80 	movzbl	-128(%rbp), %r8d
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:999
; .message_name = data.message_name_constant,
    12f8:	4c 8b 65 88 	movq	-120(%rbp), %r12
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1001
; .flag = data.flags_constant.flag,
    12fc:	0f b6 7d 90 	movzbl	-112(%rbp), %edi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1002
; .dup_flag = data.flags_constant.dup_flag,
    1300:	0f b6 75 91 	movzbl	-111(%rbp), %esi
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1003
; .qos_flag = data.flags_constant.qos_flag,
    1304:	0f b6 4d 92 	movzbl	-110(%rbp), %ecx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1004
; .retain_flag = data.flags_constant.retain_flag
    1308:	0f b6 55 93 	movzbl	-109(%rbp), %edx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1006
; .remaining_length = s._remaining_length,
    130c:	8b 5d 14 	movl	20(%rbp), %ebx
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:996
; (
    130f:	44 8b 1d 00 00 00 00 	movl	(%rip), %r11d
    1316:	44 8b 15 00 00 00 00 	movl	(%rip), %r10d
    131d:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    1324:	4c 8b 0d 00 00 00 00 	movq	(%rip), %r9
    132b:	4c 8b ad 18 ff ff ff 	movq	-232(%rbp), %r13
    1332:	45 88 45 00 	movb	%r8b, (%r13)
    1336:	4c 8b 85 18 ff ff ff 	movq	-232(%rbp), %r8
    133d:	4d 89 60 08 	movq	%r12, 8(%r8)
    1341:	4c 8b 85 18 ff ff ff 	movq	-232(%rbp), %r8
    1348:	41 88 78 10 	movb	%dil, 16(%r8)
    134c:	48 8b bd 18 ff ff ff 	movq	-232(%rbp), %rdi
    1353:	40 88 77 11 	movb	%sil, 17(%rdi)
    1357:	48 8b b5 18 ff ff ff 	movq	-232(%rbp), %rsi
    135e:	88 4e 12 	movb	%cl, 18(%rsi)
    1361:	48 8b 8d 18 ff ff ff 	movq	-232(%rbp), %rcx
    1368:	88 51 13 	movb	%dl, 19(%rcx)
    136b:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    1372:	89 5a 14 	movl	%ebx, 20(%rdx)
    1375:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    137c:	44 89 5a 18 	movl	%r11d, 24(%rdx)
    1380:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    1387:	48 8d 0d 00 00 00 00 	leaq	(%rip), %rcx
    138e:	48 89 4a 20 	movq	%rcx, 32(%rdx)
    1392:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    1399:	44 89 52 28 	movl	%r10d, 40(%rdx)
    139d:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    13a4:	48 8d 0d 00 00 00 00 	leaq	(%rip), %rcx
    13ab:	48 89 4a 30 	movq	%rcx, 48(%rdx)
    13af:	48 8b 95 18 ff ff ff 	movq	-232(%rbp), %rdx
    13b6:	88 42 38 	movb	%al, 56(%rdx)
    13b9:	48 8b 85 18 ff ff ff 	movq	-232(%rbp), %rax
    13c0:	4c 89 48 40 	movq	%r9, 64(%rax)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1017
; }
    13c4:	48 8b 85 18 ff ff ff 	movq	-232(%rbp), %rax
    13cb:	48 8d 65 e0 	leaq	-32(%rbp), %rsp
    13cf:	5b 	popq	%rbx
    13d0:	41 5c 	popq	%r12
    13d2:	41 5d 	popq	%r13
    13d4:	41 5e 	popq	%r14
    13d6:	5d 	popq	%rbp
    13d7:	c3 	retq

_mqtt_packet_parse:
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1020
; {
    13d8:	55 	pushq	%rbp
    13d9:	48 89 e5 	movq	%rsp, %rbp
    13dc:	49 c7 c3 00 f0 ff ff 	movq	$-4096, %r11
    13e3:	49 81 eb 00 10 00 00 	subq	$4096, %r11
    13ea:	4a 83 0c 1c 00 	orq	$0, (%rsp,%r11)
    13ef:	49 81 fb 00 f0 fe ff 	cmpq	$-69632, %r11
    13f6:	75 eb 	jne	-21 <_mqtt_packet_parse+0xb>
    13f8:	4a 83 8c 1c e0 fe ff ff 00 	orq	$0, -288(%rsp,%r11)
    1401:	48 81 ec 20 01 01 00 	subq	$65824, %rsp
    1408:	48 89 bd f8 fe fe ff 	movq	%rdi, -65800(%rbp)
    140f:	48 89 b5 f0 fe fe ff 	movq	%rsi, -65808(%rbp)
    1416:	89 95 ec fe fe ff 	movl	%edx, -65812(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1021
; bool ptr_is_break = false;
    141c:	c6 45 ff 00 	movb	$0, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1022
; uint8_t ptr_fixed_header_first_one_byte = (uint8_t)0U;
    1420:	c6 45 fe 00 	movb	$0, -2(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1023
; uint8_t ptr_message_type = max_u8;
    1424:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    142b:	88 45 fd 	movb	%al, -3(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1024
; bool ptris_searching_remaining_length = true;
    142e:	c6 45 fc 01 	movb	$1, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1025
; uint8_t ptr_for_decoding_packets[4U] = { 0U };
    1432:	c7 85 3e ff ff ff 00 00 00 00 	movl	$0, -194(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1026
; uint32_t ptr_remaining_length = (uint32_t)0U;
    143c:	c7 45 f8 00 00 00 00 	movl	$0, -8(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1027
; uint32_t ptr_variable_header_index = (uint32_t)0U;
    1443:	c7 45 f4 00 00 00 00 	movl	$0, -12(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1028
; uint8_t ptr_for_topic_length = (uint8_t)0U;
    144a:	c6 45 f3 00 	movb	$0, -13(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1029
; uint32_t ptr_topic_length = max_u32;
    144e:	8b 05 00 00 00 00 	movl	(%rip), %eax
    1454:	89 45 ec 	movl	%eax, -20(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1030
; uint8_t ptr_topic_name_u8[65536U] = { 0U };
    1457:	48 c7 85 30 ff fe ff 00 00 00 00 	movq	$0, -65744(%rbp)
    1462:	48 8d 85 38 ff fe ff 	leaq	-65736(%rbp), %rax
    1469:	ba f8 ff 00 00 	movl	$65528, %edx
    146e:	be 00 00 00 00 	movl	$0, %esi
    1473:	48 89 c7 	movq	%rax, %rdi
    1476:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0xa3>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1031
; C_String_t ptr_topic_name = "";
    147b:	48 8d 05 00 00 00 00 	leaq	(%rip), %rax
    1482:	48 89 45 e0 	movq	%rax, -32(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1032
; uint8_t ptr_topic_name_error_status = (uint8_t)0U;
    1486:	c6 45 df 00 	movb	$0, -33(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1033
; uint32_t ptr_property_length = (uint32_t)0U;
    148a:	c7 45 d8 00 00 00 00 	movl	$0, -40(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1034
; bool ptris_searching_property_length = true;
    1491:	c6 45 d7 01 	movb	$1, -41(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1035
; C_String_t ptr_payload = "";
    1495:	48 8d 05 00 00 00 00 	leaq	(%rip), %rax
    149c:	48 89 45 c8 	movq	%rax, -56(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1036
; uint8_t ptr_payload_error_status = (uint8_t)0U;
    14a0:	c6 45 c7 00 	movb	$0, -57(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1037
; for (uint32_t i = (uint32_t)0U; i < packet_size; i = i + (uint32_t)1U)
    14a4:	c7 45 c0 00 00 00 00 	movl	$0, -64(%rbp)
    14ab:	e9 a3 03 00 00 	jmp	931 <_mqtt_packet_parse+0x47b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1039
; uint8_t one_byte = request[i];
    14b0:	8b 45 c0 	movl	-64(%rbp), %eax
    14b3:	48 8b 95 f0 fe fe ff 	movq	-65808(%rbp), %rdx
    14ba:	48 01 d0 	addq	%rdx, %rax
    14bd:	0f b6 00 	movzbl	(%rax), %eax
    14c0:	88 45 86 	movb	%al, -122(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1040
; bool is_searching_remaining_length = ptris_searching_remaining_length;
    14c3:	0f b6 45 fc 	movzbl	-4(%rbp), %eax
    14c7:	88 45 85 	movb	%al, -123(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1041
; bool is_break = ptr_is_break;
    14ca:	0f b6 45 ff 	movzbl	-1(%rbp), %eax
    14ce:	88 45 84 	movb	%al, -124(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1042
; if (!is_break)
    14d1:	0f b6 45 84 	movzbl	-124(%rbp), %eax
    14d5:	83 f0 01 	xorl	$1, %eax
    14d8:	84 c0 	testb	%al, %al
    14da:	0f 84 6f 03 00 00 	je	879 <_mqtt_packet_parse+0x477>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1043
; if (i == (uint32_t)0U)
    14e0:	83 7d c0 00 	cmpl	$0, -64(%rbp)
    14e4:	75 60 	jne	96 <_mqtt_packet_parse+0x16e>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1045
; uint8_t message_type_bits = slice_byte(one_byte, (uint8_t)0U, (uint8_t)4U);
    14e6:	0f b6 45 86 	movzbl	-122(%rbp), %eax
    14ea:	ba 04 00 00 00 	movl	$4, %edx
    14ef:	be 00 00 00 00 	movl	$0, %esi
    14f4:	89 c7 	movl	%eax, %edi
    14f6:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x123>
    14fb:	88 85 43 ff ff ff 	movb	%al, -189(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1046
; uint8_t message_type = get_message_type(message_type_bits);
    1501:	0f b6 85 43 ff ff ff 	movzbl	-189(%rbp), %eax
    1508:	89 c7 	movl	%eax, %edi
    150a:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x137>
    150f:	88 85 42 ff ff ff 	movb	%al, -190(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1047
; ptr_message_type = message_type;
    1515:	0f b6 85 42 ff ff ff 	movzbl	-190(%rbp), %eax
    151c:	88 45 fd 	movb	%al, -3(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1048
; ptr_fixed_header_first_one_byte = one_byte;
    151f:	0f b6 45 86 	movzbl	-122(%rbp), %eax
    1523:	88 45 fe 	movb	%al, -2(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1049
; if (message_type == max_u8)
    1526:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    152d:	38 85 42 ff ff ff 	cmpb	%al, -190(%rbp)
    1533:	0f 85 16 03 00 00 	jne	790 <_mqtt_packet_parse+0x477>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1051
; ptr_is_break = true;
    1539:	c6 45 ff 01 	movb	$1, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1052
; ptris_searching_remaining_length = false;
    153d:	c6 45 fc 00 	movb	$0, -4(%rbp)
    1541:	e9 09 03 00 00 	jmp	777 <_mqtt_packet_parse+0x477>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1055
; else if (i >= (uint32_t)1U && i <= (uint32_t)4U && is_searching_remaining_length)
    1546:	83 7d c0 00 	cmpl	$0, -64(%rbp)
    154a:	74 74 	je	116 <_mqtt_packet_parse+0x1e8>
    154c:	83 7d c0 04 	cmpl	$4, -64(%rbp)
    1550:	77 6e 	ja	110 <_mqtt_packet_parse+0x1e8>
    1552:	80 7d 85 00 	cmpb	$0, -123(%rbp)
    1556:	74 68 	je	104 <_mqtt_packet_parse+0x1e8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1057
; uint8_t i_u8 = (uint8_t)i;
    1558:	8b 45 c0 	movl	-64(%rbp), %eax
    155b:	88 45 83 	movb	%al, -125(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1058
; uint32_t i_minus_one = i - (uint32_t)1U;
    155e:	8b 45 c0 	movl	-64(%rbp), %eax
    1561:	83 e8 01 	subl	$1, %eax
    1564:	89 85 7c ff ff ff 	movl	%eax, -132(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1059
; ptr_for_decoding_packets[i_minus_one] = one_byte;
    156a:	8b 95 7c ff ff ff 	movl	-132(%rbp), %edx
    1570:	0f b6 45 86 	movzbl	-122(%rbp), %eax
    1574:	88 84 15 3e ff ff ff 	movb	%al, -194(%rbp,%rdx)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1060
; uint32_t r = get_remaining_length(i_u8, ptr_for_decoding_packets, packet_size);
    157b:	0f b6 45 83 	movzbl	-125(%rbp), %eax
    157f:	8b 95 ec fe fe ff 	movl	-65812(%rbp), %edx
    1585:	48 8d 8d 3e ff ff ff 	leaq	-194(%rbp), %rcx
    158c:	48 89 ce 	movq	%rcx, %rsi
    158f:	89 c7 	movl	%eax, %edi
    1591:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x1be>
    1596:	89 85 78 ff ff ff 	movl	%eax, -136(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1061
; if (r != max_u32)
    159c:	8b 05 00 00 00 00 	movl	(%rip), %eax
    15a2:	39 85 78 ff ff ff 	cmpl	%eax, -136(%rbp)
    15a8:	0f 84 a0 02 00 00 	je	672 <_mqtt_packet_parse+0x476>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1063
; ptris_searching_remaining_length = false;
    15ae:	c6 45 fc 00 	movb	$0, -4(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1064
; ptr_remaining_length = r;
    15b2:	8b 85 78 ff ff ff 	movl	-136(%rbp), %eax
    15b8:	89 45 f8 	movl	%eax, -8(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1056
; {
    15bb:	e9 8e 02 00 00 	jmp	654 <_mqtt_packet_parse+0x476>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1067
; else if (!is_searching_remaining_length)
    15c0:	0f b6 45 85 	movzbl	-123(%rbp), %eax
    15c4:	83 f0 01 	xorl	$1, %eax
    15c7:	84 c0 	testb	%al, %al
    15c9:	0f 84 80 02 00 00 	je	640 <_mqtt_packet_parse+0x477>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1069
; uint32_t variable_header_index = ptr_variable_header_index;
    15cf:	8b 45 f4 	movl	-12(%rbp), %eax
    15d2:	89 85 74 ff ff ff 	movl	%eax, -140(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1070
; uint8_t message_type = ptr_message_type;
    15d8:	0f b6 45 fd 	movzbl	-3(%rbp), %eax
    15dc:	88 85 73 ff ff ff 	movb	%al, -141(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1071
; uint32_t topic_length = ptr_topic_length;
    15e2:	8b 45 ec 	movl	-20(%rbp), %eax
    15e5:	89 85 6c ff ff ff 	movl	%eax, -148(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1072
; if (message_type == define_mqtt_control_packet_PUBLISH)
    15eb:	0f b6 05 00 00 00 00 	movzbl	(%rip), %eax
    15f2:	38 85 73 ff ff ff 	cmpb	%al, -141(%rbp)
    15f8:	0f 85 31 02 00 00 	jne	561 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1073
; if (variable_header_index == (uint32_t)0U)
    15fe:	83 bd 74 ff ff ff 00 	cmpl	$0, -140(%rbp)
    1605:	75 0c 	jne	12 <_mqtt_packet_parse+0x23b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1074
; ptr_for_topic_length = one_byte;
    1607:	0f b6 45 86 	movzbl	-122(%rbp), %eax
    160b:	88 45 f3 	movb	%al, -13(%rbp)
    160e:	e9 1c 02 00 00 	jmp	540 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1075
; else if (variable_header_index == (uint32_t)1U)
    1613:	83 bd 74 ff ff ff 01 	cmpl	$1, -140(%rbp)
    161a:	75 73 	jne	115 <_mqtt_packet_parse+0x2b7>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1077
; uint8_t msb_u8 = ptr_for_topic_length;
    161c:	0f b6 45 f3 	movzbl	-13(%rbp), %eax
    1620:	88 85 52 ff ff ff 	movb	%al, -174(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1078
; uint8_t lsb_u8 = one_byte;
    1626:	0f b6 45 86 	movzbl	-122(%rbp), %eax
    162a:	88 85 51 ff ff ff 	movb	%al, -175(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1079
; uint32_t msb_u32 = (uint32_t)msb_u8;
    1630:	0f b6 85 52 ff ff ff 	movzbl	-174(%rbp), %eax
    1637:	89 85 4c ff ff ff 	movl	%eax, -180(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1080
; uint32_t lsb_u32 = (uint32_t)lsb_u8;
    163d:	0f b6 85 51 ff ff ff 	movzbl	-175(%rbp), %eax
    1644:	89 85 48 ff ff ff 	movl	%eax, -184(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1081
; uint32_t _topic_length = msb_u32 << (uint32_t)8U | lsb_u32;
    164a:	8b 85 4c ff ff ff 	movl	-180(%rbp), %eax
    1650:	c1 e0 08 	shll	$8, %eax
    1653:	0b 85 48 ff ff ff 	orl	-184(%rbp), %eax
    1659:	89 85 44 ff ff ff 	movl	%eax, -188(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1082
; if (_topic_length > (uint32_t)65535U)
    165f:	81 bd 44 ff ff ff ff ff 00 00 	cmpl	$65535, -188(%rbp)
    1669:	76 16 	jbe	22 <_mqtt_packet_parse+0x2a9>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1084
; ptr_topic_length = max_u32;
    166b:	8b 05 00 00 00 00 	movl	(%rip), %eax
    1671:	89 45 ec 	movl	%eax, -20(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1085
; ptr_is_break = true;
    1674:	c6 45 ff 01 	movb	$1, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1086
; ptris_searching_remaining_length = false;
    1678:	c6 45 fc 00 	movb	$0, -4(%rbp)
    167c:	e9 ae 01 00 00 	jmp	430 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1089
; ptr_topic_length = _topic_length;
    1681:	8b 85 44 ff ff ff 	movl	-188(%rbp), %eax
    1687:	89 45 ec 	movl	%eax, -20(%rbp)
    168a:	e9 a0 01 00 00 	jmp	416 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1091
; else if (variable_header_index >= (uint32_t)2U)
    168f:	83 bd 74 ff ff ff 01 	cmpl	$1, -140(%rbp)
    1696:	0f 86 93 01 00 00 	jbe	403 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1093
; bool is_searching_property_length = ptris_searching_property_length;
    169c:	0f b6 45 d7 	movzbl	-41(%rbp), %eax
    16a0:	88 85 6b ff ff ff 	movb	%al, -149(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1094
; if (topic_length == max_u32)
    16a6:	8b 05 00 00 00 00 	movl	(%rip), %eax
    16ac:	39 85 6c ff ff ff 	cmpl	%eax, -148(%rbp)
    16b2:	75 16 	jne	22 <_mqtt_packet_parse+0x2f2>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1096
; ptr_topic_length = max_u32;
    16b4:	8b 05 00 00 00 00 	movl	(%rip), %eax
    16ba:	89 45 ec 	movl	%eax, -20(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1097
; ptr_is_break = true;
    16bd:	c6 45 ff 01 	movb	$1, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1098
; ptris_searching_remaining_length = false;
    16c1:	c6 45 fc 00 	movb	$0, -4(%rbp)
    16c5:	e9 65 01 00 00 	jmp	357 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1100
; else if (variable_header_index <= topic_length + (uint32_t)1U)
    16ca:	8b 85 6c ff ff ff 	movl	-148(%rbp), %eax
    16d0:	83 c0 01 	addl	$1, %eax
    16d3:	39 85 74 ff ff ff 	cmpl	%eax, -140(%rbp)
    16d9:	77 67 	ja	103 <_mqtt_packet_parse+0x36a>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1102
; ptr_topic_name_u8[variable_header_index - (uint32_t)2U] = one_byte;
    16db:	8b 85 74 ff ff ff 	movl	-140(%rbp), %eax
    16e1:	83 e8 02 	subl	$2, %eax
    16e4:	89 c2 	movl	%eax, %edx
    16e6:	0f b6 45 86 	movzbl	-122(%rbp), %eax
    16ea:	88 84 15 30 ff fe ff 	movb	%al, -65744(%rbp,%rdx)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1103
; if (variable_header_index == topic_length + (uint32_t)1U)
    16f1:	8b 85 6c ff ff ff 	movl	-148(%rbp), %eax
    16f7:	83 c0 01 	addl	$1, %eax
    16fa:	39 85 74 ff ff ff 	cmpl	%eax, -140(%rbp)
    1700:	0f 85 29 01 00 00 	jne	297 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1106
; if (ptr_topic_name_u8[65535U] == (uint8_t)0U)
    1706:	0f b6 85 2f ff ff ff 	movzbl	-209(%rbp), %eax
    170d:	84 c0 	testb	%al, %al
    170f:	75 15 	jne	21 <_mqtt_packet_parse+0x34e>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1107
; topic_name = Utils_topic_name_uint8_to_c_string(ptr_topic_name_u8);
    1711:	48 8d 85 30 ff fe ff 	leaq	-65744(%rbp), %rax
    1718:	48 89 c7 	movq	%rax, %rdi
    171b:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x348>
    1720:	48 89 45 b8 	movq	%rax, -72(%rbp)
    1724:	eb 0f 	jmp	15 <_mqtt_packet_parse+0x35d>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1110
; ptr_topic_name_error_status = (uint8_t)1U;
    1726:	c6 45 df 01 	movb	$1, -33(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1111
; topic_name = "";
    172a:	48 8d 05 00 00 00 00 	leaq	(%rip), %rax
    1731:	48 89 45 b8 	movq	%rax, -72(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1113
; ptr_topic_name = topic_name;
    1735:	48 8b 45 b8 	movq	-72(%rbp), %rax
    1739:	48 89 45 e0 	movq	%rax, -32(%rbp)
    173d:	e9 ed 00 00 00 	jmp	237 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1119
; > topic_length + (uint32_t)1U
    1742:	8b 85 6c ff ff ff 	movl	-148(%rbp), %eax
    1748:	83 c0 01 	addl	$1, %eax
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1117
; (
    174b:	39 85 74 ff ff ff 	cmpl	%eax, -140(%rbp)
    1751:	76 34 	jbe	52 <_mqtt_packet_parse+0x3af>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1120
; && variable_header_index <= topic_length + (uint32_t)5U
    1753:	8b 85 6c ff ff ff 	movl	-148(%rbp), %eax
    1759:	83 c0 05 	addl	$5, %eax
    175c:	39 85 74 ff ff ff 	cmpl	%eax, -140(%rbp)
    1762:	77 23 	ja	35 <_mqtt_packet_parse+0x3af>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1121
; && is_searching_property_length
    1764:	80 bd 6b ff ff ff 00 	cmpb	$0, -149(%rbp)
    176b:	74 1a 	je	26 <_mqtt_packet_parse+0x3af>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1124
; if (one_byte == (uint8_t)0U)
    176d:	80 7d 86 00 	cmpb	$0, -122(%rbp)
    1771:	0f 85 b8 00 00 00 	jne	184 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1126
; ptr_property_length = (uint32_t)one_byte;
    1777:	0f b6 45 86 	movzbl	-122(%rbp), %eax
    177b:	89 45 d8 	movl	%eax, -40(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1127
; ptris_searching_property_length = false;
    177e:	c6 45 d7 00 	movb	$0, -41(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1124
; if (one_byte == (uint8_t)0U)
    1782:	e9 a8 00 00 00 	jmp	168 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1130
; else if (!is_searching_property_length)
    1787:	0f b6 85 6b ff ff ff 	movzbl	-149(%rbp), %eax
    178e:	83 f0 01 	xorl	$1, %eax
    1791:	84 c0 	testb	%al, %al
    1793:	0f 84 96 00 00 00 	je	150 <_mqtt_packet_parse+0x457>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1132
; uint32_t payload_offset = i;
    1799:	8b 45 c0 	movl	-64(%rbp), %eax
    179c:	89 85 64 ff ff ff 	movl	%eax, -156(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1133
; uint8_t *ptr_payload_u8 = request + payload_offset;
    17a2:	8b 85 64 ff ff ff 	movl	-156(%rbp), %eax
    17a8:	48 8b 95 f0 fe fe ff 	movq	-65808(%rbp), %rdx
    17af:	48 01 d0 	addq	%rdx, %rax
    17b2:	48 89 85 58 ff ff ff 	movq	%rax, -168(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1134
; uint32_t last_payload_index = packet_size - payload_offset;
    17b9:	8b 85 ec fe fe ff 	movl	-65812(%rbp), %eax
    17bf:	2b 85 64 ff ff ff 	subl	-156(%rbp), %eax
    17c5:	89 85 54 ff ff ff 	movl	%eax, -172(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1135
; uint8_t last_payload_element = ptr_payload_u8[last_payload_index];
    17cb:	8b 85 54 ff ff ff 	movl	-172(%rbp), %eax
    17d1:	48 8b 95 58 ff ff ff 	movq	-168(%rbp), %rdx
    17d8:	48 01 d0 	addq	%rdx, %rax
    17db:	0f b6 00 	movzbl	(%rax), %eax
    17de:	88 85 53 ff ff ff 	movb	%al, -173(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1137
; if (last_payload_element != (uint8_t)0U)
    17e4:	80 bd 53 ff ff ff 00 	cmpb	$0, -173(%rbp)
    17eb:	74 11 	je	17 <_mqtt_packet_parse+0x426>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1139
; ptr_payload_error_status = (uint8_t)1U;
    17ed:	c6 45 c7 01 	movb	$1, -57(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1140
; payload = "";
    17f1:	48 8d 05 00 00 00 00 	leaq	(%rip), %rax
    17f8:	48 89 45 b0 	movq	%rax, -80(%rbp)
    17fc:	eb 25 	jmp	37 <_mqtt_packet_parse+0x44b>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1144
; Utils_payload_uint8_to_c_string(ptr_payload_u8,
    17fe:	8b 15 00 00 00 00 	movl	(%rip), %edx
    1804:	8b 35 00 00 00 00 	movl	(%rip), %esi
    180a:	8b 8d ec fe fe ff 	movl	-65812(%rbp), %ecx
    1810:	48 8b 85 58 ff ff ff 	movq	-168(%rbp), %rax
    1817:	48 89 c7 	movq	%rax, %rdi
    181a:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x447>
    181f:	48 89 45 b0 	movq	%rax, -80(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1148
; ptr_payload = payload;
    1823:	48 8b 45 b0 	movq	-80(%rbp), %rax
    1827:	48 89 45 c8 	movq	%rax, -56(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1149
; ptr_is_break = true;
    182b:	c6 45 ff 01 	movb	$1, -1(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1152
; if (variable_header_index <= max_u32 - (uint32_t)1U)
    182f:	8b 05 00 00 00 00 	movl	(%rip), %eax
    1835:	83 e8 01 	subl	$1, %eax
    1838:	39 85 74 ff ff ff 	cmpl	%eax, -140(%rbp)
    183e:	77 0f 	ja	15 <_mqtt_packet_parse+0x477>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1153
; ptr_variable_header_index = variable_header_index + (uint32_t)1U;
    1840:	8b 85 74 ff ff ff 	movl	-140(%rbp), %eax
    1846:	83 c0 01 	addl	$1, %eax
    1849:	89 45 f4 	movl	%eax, -12(%rbp)
    184c:	eb 01 	jmp	1 <_mqtt_packet_parse+0x477>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1056
; {
    184e:	90 	nop
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1037
; for (uint32_t i = (uint32_t)0U; i < packet_size; i = i + (uint32_t)1U)
    184f:	83 45 c0 01 	addl	$1, -64(%rbp)
    1853:	8b 45 c0 	movl	-64(%rbp), %eax
    1856:	3b 85 ec fe fe ff 	cmpl	-65812(%rbp), %eax
    185c:	0f 82 4e fc ff ff 	jb	-946 <_mqtt_packet_parse+0xd8>
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1156
; bool is_searching_remaining_length = ptris_searching_remaining_length;
    1862:	0f b6 45 fc 	movzbl	-4(%rbp), %eax
    1866:	88 45 af 	movb	%al, -81(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1157
; uint8_t fixed_header_first_one_byte = ptr_fixed_header_first_one_byte;
    1869:	0f b6 45 fe 	movzbl	-2(%rbp), %eax
    186d:	88 45 ae 	movb	%al, -82(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1158
; uint8_t message_type = ptr_message_type;
    1870:	0f b6 45 fd 	movzbl	-3(%rbp), %eax
    1874:	88 45 ad 	movb	%al, -83(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1159
; uint32_t remaining_length = ptr_remaining_length;
    1877:	8b 45 f8 	movl	-8(%rbp), %eax
    187a:	89 45 a8 	movl	%eax, -88(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1160
; uint32_t topic_length = ptr_topic_length;
    187d:	8b 45 ec 	movl	-20(%rbp), %eax
    1880:	89 45 a4 	movl	%eax, -92(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1161
; C_String_t topic_name = ptr_topic_name;
    1883:	48 8b 45 e0 	movq	-32(%rbp), %rax
    1887:	48 89 45 98 	movq	%rax, -104(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1162
; uint8_t topic_name_error_status = ptr_topic_name_error_status;
    188b:	0f b6 45 df 	movzbl	-33(%rbp), %eax
    188f:	88 45 97 	movb	%al, -105(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1163
; bool is_searching_property_length = ptris_searching_property_length;
    1892:	0f b6 45 d7 	movzbl	-41(%rbp), %eax
    1896:	88 45 96 	movb	%al, -106(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1164
; uint32_t property_length = ptr_property_length;
    1899:	8b 45 d8 	movl	-40(%rbp), %eax
    189c:	89 45 90 	movl	%eax, -112(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1165
; C_String_t payload = ptr_payload;
    189f:	48 8b 45 c8 	movq	-56(%rbp), %rax
    18a3:	48 89 45 88 	movq	%rax, -120(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1166
; uint8_t payload_error_status = ptr_payload_error_status;
    18a7:	0f b6 45 c7 	movzbl	-57(%rbp), %eax
    18ab:	88 45 87 	movb	%al, -121(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1168
; ed_fixed_header_parts =
    18ae:	0f b6 45 ae 	movzbl	-82(%rbp), %eax
    18b2:	88 85 00 ff fe ff 	movb	%al, -65792(%rbp)
    18b8:	0f b6 45 af 	movzbl	-81(%rbp), %eax
    18bc:	88 85 01 ff fe ff 	movb	%al, -65791(%rbp)
    18c2:	0f b6 45 96 	movzbl	-106(%rbp), %eax
    18c6:	88 85 02 ff fe ff 	movb	%al, -65790(%rbp)
    18cc:	0f b6 45 ad 	movzbl	-83(%rbp), %eax
    18d0:	88 85 03 ff fe ff 	movb	%al, -65789(%rbp)
    18d6:	8b 45 a8 	movl	-88(%rbp), %eax
    18d9:	89 85 04 ff fe ff 	movl	%eax, -65788(%rbp)
    18df:	8b 45 a4 	movl	-92(%rbp), %eax
    18e2:	89 85 08 ff fe ff 	movl	%eax, -65784(%rbp)
    18e8:	48 8b 45 98 	movq	-104(%rbp), %rax
    18ec:	48 89 85 10 ff fe ff 	movq	%rax, -65776(%rbp)
    18f3:	0f b6 45 97 	movzbl	-105(%rbp), %eax
    18f7:	88 85 18 ff fe ff 	movb	%al, -65768(%rbp)
    18fd:	8b 45 90 	movl	-112(%rbp), %eax
    1900:	89 85 1c ff fe ff 	movl	%eax, -65764(%rbp)
    1906:	48 8b 45 88 	movq	-120(%rbp), %rax
    190a:	48 89 85 20 ff fe ff 	movq	%rax, -65760(%rbp)
    1911:	0f b6 45 87 	movzbl	-121(%rbp), %eax
    1915:	88 85 28 ff fe ff 	movb	%al, -65752(%rbp)
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1178
; return get_fixed_header(ed_fixed_header_parts);
    191b:	48 8b 85 f8 fe fe ff 	movq	-65800(%rbp), %rax
    1922:	ff b5 28 ff fe ff 	pushq	-65752(%rbp)
    1928:	ff b5 20 ff fe ff 	pushq	-65760(%rbp)
    192e:	ff b5 18 ff fe ff 	pushq	-65768(%rbp)
    1934:	ff b5 10 ff fe ff 	pushq	-65776(%rbp)
    193a:	ff b5 08 ff fe ff 	pushq	-65784(%rbp)
    1940:	ff b5 00 ff fe ff 	pushq	-65792(%rbp)
    1946:	48 89 c7 	movq	%rax, %rdi
    1949:	e8 00 00 00 00 	callq	0 <_mqtt_packet_parse+0x576>
    194e:	48 83 c4 30 	addq	$48, %rsp
; /Users/kitamurataku/work/verimqtt/src/./out/Main.c:1179
; }
    1952:	48 8b 85 f8 fe fe ff 	movq	-65800(%rbp), %rax
    1959:	c9 	leave
    195a:	c3 	retq
