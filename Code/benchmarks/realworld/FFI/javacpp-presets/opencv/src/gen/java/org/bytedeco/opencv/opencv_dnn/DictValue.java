// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.opencv.opencv_dnn;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import static org.bytedeco.openblas.global.openblas_nolapack.*;
import static org.bytedeco.openblas.global.openblas.*;
import org.bytedeco.opencv.opencv_core.*;
import static org.bytedeco.opencv.global.opencv_core.*;
import org.bytedeco.opencv.opencv_imgproc.*;
import static org.bytedeco.opencv.global.opencv_imgproc.*;

import static org.bytedeco.opencv.global.opencv_dnn.*;

/** \addtogroup dnn
 *  \{
<p>
/** \brief This struct stores the scalar value (or array) of one of the following type: double, cv::String or int64.
 *  \todo Maybe int64 is useless because double type exactly stores at least 2^52 integers.
 */
@Namespace("cv::dnn") @NoOffset @Properties(inherit = org.bytedeco.opencv.presets.opencv_dnn.class)
public class DictValue extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public DictValue(Pointer p) { super(p); }

    public DictValue(@Const @ByRef DictValue r) { super((Pointer)null); allocate(r); }
    private native void allocate(@Const @ByRef DictValue r);
    /** Constructs integer scalar */
    public DictValue(@Cast("bool") boolean i) { super((Pointer)null); allocate(i); }
    private native void allocate(@Cast("bool") boolean i);
    /** Constructs integer scalar */
    public DictValue(@Cast("int64") long i/*=0*/) { super((Pointer)null); allocate(i); }
    private native void allocate(@Cast("int64") long i/*=0*/);
    public DictValue() { super((Pointer)null); allocate(); }
    private native void allocate();
    /** Constructs integer scalar */
    public DictValue(int i) { super((Pointer)null); allocate(i); }
    private native void allocate(int i);
    /** Constructs floating point scalar */
    public DictValue(double p) { super((Pointer)null); allocate(p); }
    private native void allocate(double p);
    /** Constructs string scalar */
    public DictValue(@Str BytePointer s) { super((Pointer)null); allocate(s); }
    private native void allocate(@Str BytePointer s);
    public DictValue(@Str String s) { super((Pointer)null); allocate(s); }
    private native void allocate(@Str String s);

    public native int size();

    public native @Cast("bool") boolean isInt();
    public native @Cast("bool") boolean isString();
    public native @Cast("bool") boolean isReal();

    public native int getIntValue(int idx/*=-1*/);
    public native int getIntValue();
    public native double getRealValue(int idx/*=-1*/);
    public native double getRealValue();
    public native @Str BytePointer getStringValue(int idx/*=-1*/);
    public native @Str BytePointer getStringValue();

    public native @ByRef @Name("operator =") DictValue put(@Const @ByRef DictValue r);

    
}