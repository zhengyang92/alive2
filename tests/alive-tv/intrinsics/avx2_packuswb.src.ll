define <32 x i8> @test_x86_avx2_packuswb(<16 x i16> %a0, <16 x i16> %a1) {
  %res = call <32 x i8> @llvm.x86.avx2.packuswb(<16 x i16> <i16 3000, i16 -1, i16 3, i16 4, i16 5, i16 6, i16 7, i16 8, i16 9, i16 10, i16 11, i16 12, i16 13, i16 14, i16 15, i16 16>, <16 x i16> <i16 17, i16 18, i16 19, i16 20, i16 21, i16 22, i16 23, i16 24, i16 25, i16 26, i16 27, i16 28, i16 29, i16 30, i16 31, i16 32>) ; <<16 x i16>> [#uses=1]
  ret <32 x i8> %res
}

declare <32 x i8> @llvm.x86.avx2.packuswb(<16 x i16>, <16 x i16>) nounwind readnone
