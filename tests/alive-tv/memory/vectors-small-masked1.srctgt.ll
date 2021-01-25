target datalayout="e"

define i8 @src(<3 x i2>* %p) {
  ; 00111001 = 57
  store <3 x i2> <i2 1, i2 2, i2 3>, <3 x i2>* %p
  ; 00110001 = 49
  %q = call <3 x i2> @llvm.masked.load.v3i2.p0v3i2 (<3 x i2>* %p, i32 0, <3 x i1> <i1 1, i1 0, i1 1>, <3 x i2> <i2 0, i2 0, i2 0>)
  %w = bitcast <3 x i2> %q to i6
  %v = zext i6 %w to i8
  ret i8 %v
}

define i8 @tgt(<3 x i2>* %p) {
  %p2 = bitcast <3 x i2>* %p to i8*
  store i8 57, i8* %p2
  ret i8 49
}

declare <3 x i2> @llvm.masked.load.v3i2.p0v3i2(<3 x i2>*, i32, <3 x i1>, <3 x i2>)
