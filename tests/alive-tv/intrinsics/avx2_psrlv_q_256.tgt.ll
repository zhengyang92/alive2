define <4 x i64> @test_x86_avx2_psrlv_q_256(<4 x i64> %a0, <4 x i64> %a1) {
  ret <4 x i64> <i64 16384, i64 8192, i64 4096, i64 2048>
}
declare <4 x i64> @llvm.x86.avx2.psrlv.q.256(<4 x i64>, <4 x i64>) nounwind readnone