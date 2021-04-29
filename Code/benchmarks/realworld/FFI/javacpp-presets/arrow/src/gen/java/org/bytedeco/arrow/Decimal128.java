// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.arrow;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.arrow.global.arrow.*;


/** Represents a signed 128-bit integer in two's complement.
 *  Calculations wrap around and overflow is ignored.
 *  The max decimal precision that can be safely represented is
 *  38 significant digits.
 * 
 *  For a discussion of the algorithms, look at Knuth's volume 2,
 *  Semi-numerical Algorithms section 4.3.1.
 * 
 *  Adapted from the Apache ORC C++ implementation
 * 
 *  The implementation is split into two parts :
 * 
 *  1. BasicDecimal128
 *     - can be safely compiled to IR without references to libstdc++.
 *  2. Decimal128
 *     - has additional functionality on top of BasicDecimal128 to deal with
 *       strings and streams. */
@Namespace("arrow") @Properties(inherit = org.bytedeco.arrow.presets.arrow.class)
public class Decimal128 extends BasicDecimal128 {
    static { Loader.load(); }

  
    public Decimal128(@Cast("int64_t") long high, @Cast("uint64_t") long low) { super((Pointer)null); allocate(high, low); }
    @NoException private native void allocate(@Cast("int64_t") long high, @Cast("uint64_t") long low);
    public Decimal128() { super((Pointer)null); allocate(); }
    @NoException private native void allocate();
    public Decimal128(@Cast("const uint8_t*") BytePointer bytes) { super((Pointer)null); allocate(bytes); }
    private native void allocate(@Cast("const uint8_t*") BytePointer bytes);
    public Decimal128(@Cast("const uint8_t*") ByteBuffer bytes) { super((Pointer)null); allocate(bytes); }
    private native void allocate(@Cast("const uint8_t*") ByteBuffer bytes);
    public Decimal128(@Cast("const uint8_t*") byte[] bytes) { super((Pointer)null); allocate(bytes); }
    private native void allocate(@Cast("const uint8_t*") byte[] bytes);
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public Decimal128(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public Decimal128(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public Decimal128 position(long position) {
        return (Decimal128)super.position(position);
    }
    @Override public Decimal128 getPointer(long i) {
        return new Decimal128((Pointer)this).position(position + i);
    }

  /** \cond FALSE */
  // (need to avoid a duplicate definition in Sphinx)
  /** \endcond
   <p>
   *  \brief constructor creates a Decimal128 from a BasicDecimal128. */
  public Decimal128(@Const @ByRef BasicDecimal128 value) { super((Pointer)null); allocate(value); }
  @NoException private native void allocate(@Const @ByRef BasicDecimal128 value);

  /** \brief Parse the number from a base 10 string representation. */
  public Decimal128(@StdString String value) { super((Pointer)null); allocate(value); }
  private native void allocate(@StdString String value);

  /** \brief Empty constructor creates a Decimal128 with a value of 0. */
  // This is required on some older compilers.

  /** Divide this number by right and return the result.
   * 
   *  This operation is not destructive.
   *  The answer rounds to zero. Signs work like:
   *    21 /  5 ->  4,  1
   *   -21 /  5 -> -4, -1
   *    21 / -5 -> -4,  1
   *   -21 / -5 ->  4, -1
   *  @param divisor [in] the number to divide by
   *  @return the pair of the quotient and the remainder */
  public native @ByVal Decimal128PairResult Divide(@Const @ByRef Decimal128 divisor);

  /** \brief Convert the Decimal128 value to a base 10 decimal string with the given
   *  scale. */
  public native @StdString String ToString(int scale);

  /** \brief Convert the value to an integer string */
  public native @StdString String ToIntegerString();

  /** \brief Cast this value to an int64_t. */
  public native @Cast("int64_t") @Name("operator int64_t") long asLong();

  /** \brief Convert a decimal string to a Decimal128 value, optionally including
   *  precision and scale if they're passed in and not null. */
  public static native @ByVal Status FromString(@StdString String s, Decimal128 out, IntPointer precision,
                             IntPointer scale/*=nullptr*/);
  public static native @ByVal Status FromString(@StdString String s, Decimal128 out, IntPointer precision);
  public static native @ByVal Status FromString(@StdString BytePointer s, Decimal128 out, IntBuffer precision,
                             IntBuffer scale/*=nullptr*/);
  public static native @ByVal Status FromString(@StdString BytePointer s, Decimal128 out, IntBuffer precision);
  public static native @ByVal Status FromString(@StdString String s, Decimal128 out, int[] precision,
                             int[] scale/*=nullptr*/);
  public static native @ByVal Status FromString(@StdString String s, Decimal128 out, int[] precision);
  public static native @ByVal Status FromString(@StdString BytePointer s, Decimal128 out, IntPointer precision,
                             IntPointer scale/*=nullptr*/);
  public static native @ByVal Status FromString(@StdString BytePointer s, Decimal128 out, IntPointer precision);
  public static native @ByVal Status FromString(@StdString String s, Decimal128 out, IntBuffer precision,
                             IntBuffer scale/*=nullptr*/);
  public static native @ByVal Status FromString(@StdString String s, Decimal128 out, IntBuffer precision);
  public static native @ByVal Status FromString(@StdString BytePointer s, Decimal128 out, int[] precision,
                             int[] scale/*=nullptr*/);
  public static native @ByVal Status FromString(@StdString BytePointer s, Decimal128 out, int[] precision);
  public static native @ByVal Decimal128Result FromString(@StdString String s);
  public static native @ByVal Decimal128Result FromString(@StdString BytePointer s);

  public static native @ByVal Decimal128Result FromReal(double real, int precision, int scale);
  public static native @ByVal Decimal128Result FromReal(float real, int precision, int scale);

  /** \brief Convert from a big-endian byte representation. The length must be
   *         between 1 and 16.
   *  @return error status if the length is an invalid value */
  public static native @ByVal Decimal128Result FromBigEndian(@Cast("const uint8_t*") BytePointer data, int length);
  public static native @ByVal Decimal128Result FromBigEndian(@Cast("const uint8_t*") ByteBuffer data, int length);
  public static native @ByVal Decimal128Result FromBigEndian(@Cast("const uint8_t*") byte[] data, int length);

  /** \brief Convert Decimal128 from one scale to another */
  public native @ByVal Decimal128Result Rescale(int original_scale, int new_scale);

  /** \brief Convert to a signed integer */

  /** \brief Convert to a signed integer */

  /** \brief Convert to a floating-point number (scaled) */
  public native float ToFloat(int scale);
  /** \brief Convert to a floating-point number (scaled) */
  public native double ToDouble(int scale);

  /** \brief Convert to a floating-point number (scaled) */

  
}
