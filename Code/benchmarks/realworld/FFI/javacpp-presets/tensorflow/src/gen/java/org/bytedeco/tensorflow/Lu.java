// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


/** Computes the LU decomposition of one or more square matrices.
 * 
 *  The input is a tensor of shape {@code [..., M, M]} whose inner-most 2 dimensions
 *  form square matrices.
 * 
 *  The input has to be invertible.
 * 
 *  The output consists of two tensors LU and P containing the LU decomposition
 *  of all input submatrices {@code [..., :, :]}. LU encodes the lower triangular and
 *  upper triangular factors.
 * 
 *  For each input submatrix of shape {@code [M, M]}, L is a lower triangular matrix of
 *  shape {@code [M, M]} with unit diagonal whose entries correspond to the strictly lower
 *  triangular part of LU. U is a upper triangular matrix of shape {@code [M, M]} whose
 *  entries correspond to the upper triangular part, including the diagonal, of LU.
 * 
 *  P represents a permutation matrix encoded as a list of indices each between {@code 0}
 *  and {@code M-1}, inclusive. If P_mat denotes the permutation matrix corresponding to
 *  P, then the L, U and P satisfies P_mat * input = L * U.
 * 
 *  Arguments:
 *  * scope: A Scope object
 *  * input: A tensor of shape {@code [..., M, M]} whose inner-most 2 dimensions form matrices of
 *  size {@code [M, M]}.
 * 
 *  Returns:
 *  * {@code Output} lu: A tensor of shape {@code [..., M, M]} whose strictly lower triangular part denotes the
 *  lower triangular factor {@code L} with unit diagonal, and whose upper triangular part
 *  denotes the upper triangular factor {@code U}.
 *  * {@code Output} p: Permutation of the rows encoded as a list of indices in {@code 0..M-1}. Shape is
 *  {@code [..., M]}.
 *  \compatibility(scipy)
 *  Similar to {@code scipy.linalg.lu}, except the triangular factors {@code L} and {@code U} are
 *  packed into a single tensor, the permutation is applied to {@code input} instead of
 *  the right hand side and the permutation {@code P} is returned as a list of indices
 *  instead of a permutation matrix.
 *  \end_compatibility */
@Namespace("tensorflow::ops") @NoOffset @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class Lu extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public Lu(Pointer p) { super(p); }

  /** Optional attribute setters for Lu */
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
  
    /** Defaults to DT_INT32 */
    public native @ByVal Attrs OutputIdxType(@Cast("tensorflow::DataType") int x);

    public native @Cast("tensorflow::DataType") int output_idx_type_(); public native Attrs output_idx_type_(int setter);
  }
  public Lu(@Const @ByRef Scope scope, @ByVal Input input) { super((Pointer)null); allocate(scope, input); }
  private native void allocate(@Const @ByRef Scope scope, @ByVal Input input);
  public Lu(@Const @ByRef Scope scope, @ByVal Input input, @Const @ByRef Attrs attrs) { super((Pointer)null); allocate(scope, input, attrs); }
  private native void allocate(@Const @ByRef Scope scope, @ByVal Input input, @Const @ByRef Attrs attrs);

  public static native @ByVal Attrs OutputIdxType(@Cast("tensorflow::DataType") int x);

  public native @ByRef Operation operation(); public native Lu operation(Operation setter);
  public native @ByRef Output lu(); public native Lu lu(Output setter);
  public native @ByRef Output p(); public native Lu p(Output setter);
}
