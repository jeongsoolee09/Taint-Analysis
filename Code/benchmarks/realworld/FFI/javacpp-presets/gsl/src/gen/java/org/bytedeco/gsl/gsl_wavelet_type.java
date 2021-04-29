// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.gsl;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import static org.bytedeco.openblas.global.openblas_nolapack.*;
import static org.bytedeco.openblas.global.openblas.*;

import static org.bytedeco.gsl.global.gsl.*;


@Properties(inherit = org.bytedeco.gsl.presets.gsl.class)
public class gsl_wavelet_type extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public gsl_wavelet_type() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public gsl_wavelet_type(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public gsl_wavelet_type(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public gsl_wavelet_type position(long position) {
        return (gsl_wavelet_type)super.position(position);
    }
    @Override public gsl_wavelet_type getPointer(long i) {
        return new gsl_wavelet_type(this).position(position + i);
    }

  public native @Cast("const char*") BytePointer name(); public native gsl_wavelet_type name(BytePointer setter);
  public static class Init_PointerPointer_PointerPointer_PointerPointer_PointerPointer_SizeTPointer_SizeTPointer_long extends FunctionPointer {
      static { Loader.load(); }
      /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
      public    Init_PointerPointer_PointerPointer_PointerPointer_PointerPointer_SizeTPointer_SizeTPointer_long(Pointer p) { super(p); }
      protected Init_PointerPointer_PointerPointer_PointerPointer_PointerPointer_SizeTPointer_SizeTPointer_long() { allocate(); }
      private native void allocate();
      public native int call(@Cast("const double**") PointerPointer h1, @Cast("const double**") PointerPointer g1,
                 @Cast("const double**") PointerPointer h2, @Cast("const double**") PointerPointer g2, @Cast("size_t*") SizeTPointer nc,
                 @Cast("size_t*") SizeTPointer offset, @Cast("size_t") long member);
  }
  public native Init_PointerPointer_PointerPointer_PointerPointer_PointerPointer_SizeTPointer_SizeTPointer_long init(); public native gsl_wavelet_type init(Init_PointerPointer_PointerPointer_PointerPointer_PointerPointer_SizeTPointer_SizeTPointer_long setter);
}
