target datalayout="e"

define <3 x i2> @src(<3 x i2>* %p) {
  %p2 = bitcast <3 x i2>* %p to i8*
  store i8 57, i8* %p2
  ret <3 x i2> <i2 1, i2 poison, i2 3>
}

define <3 x i2> @tgt(<3 x i2>* %p) {
  ; 00111001 = 57
  store <3 x i2> <i2 1, i2 2, i2 3>, <3 x i2>* %p
  ; 00110001 = 49
  %q = call <3 x i2> @llvm.masked.load.v3i2.p0v3i2 (<3 x i2>* %p, i32 4, <3 x i1> <i1 1, i1 poison, i1 1>, <3 x i2> <i2 0, i2 1, i2 0>)
  ret <3 x i2> %q
}


declare <3 x i2> @llvm.masked.load.v3i2.p0v3i2(<3 x i2>*, i32, <3 x i1>, <3 x i2>)
