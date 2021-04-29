// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


/** Decompress strings.
 * 
 *  This op decompresses each element of the {@code bytes} input {@code Tensor}, which
 *  is assumed to be compressed using the given {@code compression_type}.
 * 
 *  The {@code output} is a string {@code Tensor} of the same shape as {@code bytes},
 *  each element containing the decompressed data from the corresponding
 *  element in {@code bytes}.
 * 
 *  Arguments:
 *  * scope: A Scope object
 *  * bytes: A Tensor of string which is compressed.
 * 
 *  Optional attributes (see {@code Attrs}):
 *  * compression_type: A scalar containing either (i) the empty string (no
 *  compression), (ii) "ZLIB", or (iii) "GZIP".
 * 
 *  Returns:
 *  * {@code Output}: A Tensor with the same shape as input {@code bytes}, uncompressed
 *  from bytes. */
@Namespace("tensorflow::ops") @NoOffset @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class DecodeCompressed extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public DecodeCompressed(Pointer p) { super(p); }

  /** Optional attribute setters for DecodeCompressed */
  public static class Attrs extends Pointer {
      static { Loader.load(); }
      /** Default native constructor. */
      public Attrs() { super((Pointer)null); allocate(); }
      /** Native array allocator. Access with {@link Pointer#position(long)}. */
      public Attrs(long size) { super((Pointer)null); allocateArray(size); }
      /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
      public Attrs(Pointer p) { super(p); }
      private native void allocate();
      private native void allocateArray(long size);
      @Override public Attrs position(long position) {
          return (Attrs)super.position(position);
      }
      @Override public Attrs getPointer(long i) {
          return new Attrs(this).position(position + i);
      }
  
    /** A scalar containing either (i) the empty string (no
     *  compression), (ii) "ZLIB", or (iii) "GZIP".
     * 
     *  Defaults to "" */
    public native @ByVal Attrs CompressionType(@StringPiece BytePointer x);
    public native @ByVal Attrs CompressionType(@StringPiece String x);

    public native @StringPiece BytePointer compression_type_(); public native Attrs compression_type_(BytePointer setter);
  }
  public DecodeCompressed(@Const @ByRef Scope scope, @ByVal Input bytes) { super((Pointer)null); allocate(scope, bytes); }
  private native void allocate(@Const @ByRef Scope scope, @ByVal Input bytes);
  public DecodeCompressed(@Const @ByRef Scope scope, @ByVal Input bytes,
                   @Const @ByRef Attrs attrs) { super((Pointer)null); allocate(scope, bytes, attrs); }
  private native void allocate(@Const @ByRef Scope scope, @ByVal Input bytes,
                   @Const @ByRef Attrs attrs);
  public native @ByVal @Name("operator tensorflow::Output") Output asOutput();
  public native @ByVal @Name("operator tensorflow::Input") Input asInput();
  public native Node node();

  public static native @ByVal Attrs CompressionType(@StringPiece BytePointer x);
  public static native @ByVal Attrs CompressionType(@StringPiece String x);

  public native @ByRef Operation operation(); public native DecodeCompressed operation(Operation setter);
  public native @ByRef Output output(); public native DecodeCompressed output(Output setter);
}
