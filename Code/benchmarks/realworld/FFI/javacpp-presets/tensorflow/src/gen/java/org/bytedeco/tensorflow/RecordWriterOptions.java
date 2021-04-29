// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


@Namespace("tensorflow::io") @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class RecordWriterOptions extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public RecordWriterOptions() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public RecordWriterOptions(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public RecordWriterOptions(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public RecordWriterOptions position(long position) {
        return (RecordWriterOptions)super.position(position);
    }
    @Override public RecordWriterOptions getPointer(long i) {
        return new RecordWriterOptions(this).position(position + i);
    }

  /** enum tensorflow::io::RecordWriterOptions::CompressionType */
  public static final int NONE = 0, ZLIB_COMPRESSION = 1;
  public native @Cast("tensorflow::io::RecordWriterOptions::CompressionType") int compression_type(); public native RecordWriterOptions compression_type(int setter);

  public static native @ByVal RecordWriterOptions CreateRecordWriterOptions(
        @StdString BytePointer compression_type);
  public static native @ByVal RecordWriterOptions CreateRecordWriterOptions(
        @StdString String compression_type);

// Options specific to zlib compression.
// #if !defined(IS_SLIM_BUILD)
  public native @ByRef ZlibCompressionOptions zlib_options(); public native RecordWriterOptions zlib_options(ZlibCompressionOptions setter);
// #endif  // IS_SLIM_BUILD
}