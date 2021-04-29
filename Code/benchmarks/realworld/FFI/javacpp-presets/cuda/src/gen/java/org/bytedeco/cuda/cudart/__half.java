// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cuda.cudart;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.cuda.global.cudart.*;

// #endif /* defined(__GNUC__) */

@NoOffset @Properties(inherit = org.bytedeco.cuda.presets.cudart.class)
public class __half extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public __half(Pointer p) { super(p); }

// #if defined(__CPP_VERSION_AT_LEAST_11_FP16)
    public __half() { super((Pointer)null); allocate(); }
    private native void allocate();
// #else
// #endif /* defined(__CPP_VERSION_AT_LEAST_11_FP16) */

    /* Convert to/from __half_raw */
    public __half(@Const @ByRef __half_raw hr) { super((Pointer)null); allocate(hr); }
    private native void allocate(@Const @ByRef __half_raw hr);
    public native @ByRef @Name("operator =") __half put(@Const @ByRef __half_raw hr);
    public native @ByVal @Name("operator __half_raw") __half_raw as__half_raw();

// #if !defined(__CUDA_NO_HALF_CONVERSIONS__)

    /* Construct from float/double */
    public __half(float f) { super((Pointer)null); allocate(f); }
    private native void allocate(float f);
    public __half(double f) { super((Pointer)null); allocate(f); }
    private native void allocate(double f);

    public native @Name("operator float") float asFloat();
    public native @ByRef @Name("operator =") __half put(float f);

    /* We omit "cast to double" operator, so as to not be ambiguous about up-cast */
    public native @ByRef @Name("operator =") __half put(double f);

/* Member functions only available to nvcc compilation so far */
// #if defined(__CUDACC__)
// #endif /* defined(__CUDACC__) */
// #endif /* !defined(__CUDA_NO_HALF_CONVERSIONS__) */
}