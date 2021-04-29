// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.tensorflow;

import org.bytedeco.tensorflow.Allocator;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.tensorflow.global.tensorflow.*;


/** Represents an n-dimensional array of values. */
@Namespace("tensorflow") @NoOffset @Properties(inherit = org.bytedeco.tensorflow.presets.tensorflow.class)
public class Tensor extends AbstractTensor {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public Tensor(Pointer p) { super(p); }

  /** \brief Creates a 1-dimensional, 0-element float tensor.
   * 
   *  The returned Tensor is not a scalar (shape {}), but is instead
   *  an empty one-dimensional Tensor (shape {0}, NumElements() ==
   *  0). Since it has no elements, it does not need to be assigned a
   *  value and is initialized by default (IsInitialized() is
   *  true). If this is undesirable, consider creating a one-element
   *  scalar which does require initialization:
   * 
   *  <pre>{@code c++
   * 
   *      Tensor(DT_FLOAT, TensorShape({}))
   * 
   *  }</pre> */
  
  ///
  public Tensor() { super((Pointer)null); allocate(); }
  private native void allocate();

  /** \brief Creates a Tensor of the given {@code type} and {@code shape}.  If
   *  LogMemory::IsEnabled() the allocation is logged as coming from
   *  an unknown kernel and step. Calling the Tensor constructor
   *  directly from within an Op is deprecated: use the
   *  OpKernelConstruction/OpKernelContext allocate_* methods to
   *  allocate a new tensor, which record the kernel and step.
   * 
   *  The underlying buffer is allocated using a {@code CPUAllocator}. */
  
  ///
  public Tensor(@Cast("tensorflow::DataType") int type, @Const @ByRef TensorShape shape) { super((Pointer)null); allocate(type, shape); }
  private native void allocate(@Cast("tensorflow::DataType") int type, @Const @ByRef TensorShape shape);

  /** \brief Creates a tensor with the input {@code type} and {@code shape}, using
   *  the allocator {@code a} to allocate the underlying buffer. If
   *  LogMemory::IsEnabled() the allocation is logged as coming from
   *  an unknown kernel and step. Calling the Tensor constructor
   *  directly from within an Op is deprecated: use the
   *  OpKernelConstruction/OpKernelContext allocate_* methods to
   *  allocate a new tensor, which record the kernel and step.
   * 
   *  {@code a} must outlive the lifetime of this Tensor. */
  
  ///
  public Tensor(Allocator a, @Cast("tensorflow::DataType") int type, @Const @ByRef TensorShape shape) { super((Pointer)null); allocate(a, type, shape); }
  private native void allocate(Allocator a, @Cast("tensorflow::DataType") int type, @Const @ByRef TensorShape shape);

  /** \brief Creates a tensor with the input {@code type} and {@code shape}, using
   *  the allocator {@code a} and the specified "allocation_attr" to
   *  allocate the underlying buffer. If the kernel and step are known
   *  allocation_attr.allocation_will_be_logged should be set to true
   *  and LogMemory::RecordTensorAllocation should be called after the
   *  tensor is constructed. Calling the Tensor constructor directly
   *  from within an Op is deprecated: use the
   *  OpKernelConstruction/OpKernelContext allocate_* methods to
   *  allocate a new tensor, which record the kernel and step.
   * 
   *  {@code a} must outlive the lifetime of this Tensor. */
  
  ///
  public Tensor(Allocator a, @Cast("tensorflow::DataType") int type, @Const @ByRef TensorShape shape,
           @Const @ByRef AllocationAttributes allocation_attr) { super((Pointer)null); allocate(a, type, shape, allocation_attr); }
  private native void allocate(Allocator a, @Cast("tensorflow::DataType") int type, @Const @ByRef TensorShape shape,
           @Const @ByRef AllocationAttributes allocation_attr);

  /** \brief Creates a tensor with the input datatype, shape and buf.
   * 
   *  Acquires a ref on buf that belongs to this Tensor. */
  
  ///
  public Tensor(@Cast("tensorflow::DataType") int type, TensorShape shape, TensorBuffer buf) { super((Pointer)null); allocate(type, shape, buf); this.buffer = buf; }
  private native void allocate(@Cast("tensorflow::DataType") int type, @Const @ByRef TensorShape shape, TensorBuffer buf);
  private TensorBuffer buffer; // a reference to prevent deallocation
  public Tensor(@Cast("tensorflow::DataType") int type, TensorShape shape, final Pointer data) {
      this(type, shape, new TensorBuffer(data) {
          @Override public Pointer data() { return data; }
          @Override public long size() { return data.limit(); }
          @Override public TensorBuffer root_buffer() { return this; }
          @Override public void FillAllocationDescription(AllocationDescription proto) { }
      });
  }

  /** \brief Creates an empty Tensor of the given data type.
   * 
   *  Like Tensor(), returns a 1-dimensional, 0-element Tensor with
   *  IsInitialized() returning True. See the Tensor() documentation
   *  for details. */
  public Tensor(@Cast("tensorflow::DataType") int type) { super((Pointer)null); allocate(type); }
  private native void allocate(@Cast("tensorflow::DataType") int type);
  public Tensor(float scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(float scalar_value);
  public Tensor(double scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(double scalar_value);
  public Tensor(@Cast("tensorflow::uint16") short scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@Cast("tensorflow::uint16") short scalar_value);
  public Tensor(@Cast("tensorflow::uint8") byte scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@Cast("tensorflow::uint8") byte scalar_value);
  public Tensor(@StdString BytePointer scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@StdString BytePointer scalar_value);
  public Tensor(@StdString String scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@StdString String scalar_value);
  public Tensor(@ByVal @Cast("tensorflow::complex64*") FloatPointer scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@ByVal @Cast("tensorflow::complex64*") FloatPointer scalar_value);
  public Tensor(@ByVal @Cast("tensorflow::complex64*") FloatBuffer scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@ByVal @Cast("tensorflow::complex64*") FloatBuffer scalar_value);
  public Tensor(@ByVal @Cast("tensorflow::complex64*") float... scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@ByVal @Cast("tensorflow::complex64*") float... scalar_value);
  public Tensor(@ByVal @Cast("tensorflow::complex128*") DoublePointer scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@ByVal @Cast("tensorflow::complex128*") DoublePointer scalar_value);
  public Tensor(@ByVal @Cast("tensorflow::complex128*") DoubleBuffer scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@ByVal @Cast("tensorflow::complex128*") DoubleBuffer scalar_value);
  public Tensor(@ByVal @Cast("tensorflow::complex128*") double[] scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@ByVal @Cast("tensorflow::complex128*") double[] scalar_value);
  public Tensor(@Cast("tensorflow::int64") long scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@Cast("tensorflow::int64") long scalar_value);
  public Tensor(@Cast("bool") boolean scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@Cast("bool") boolean scalar_value);
  public Tensor(@ByVal bfloat16 scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@ByVal bfloat16 scalar_value);
  public Tensor(@ByVal ResourceHandle scalar_value) { super((Pointer)null); allocate(scalar_value); }
  private native void allocate(@ByVal ResourceHandle scalar_value);

  // NOTE: The `const char*` host-scalar constructor is provided as a
  // convenience because otherwise passing a string literal would surprisingly
  // construct a DT_BOOL tensor.

  /** Copy constructor. */
  public Tensor(@Const @ByRef Tensor other) { super((Pointer)null); allocate(other); }
  private native void allocate(@Const @ByRef Tensor other);

  /** \brief Move constructor. After this call, <other> is safely destructible
   *  and can be assigned to, but other calls on it (e.g. shape manipulation)
   *  are not valid. */

  /** Returns the data type. */
  public native @Cast("tensorflow::DataType") int dtype();

  /** Returns the shape of the tensor. */
  
  ///
  public native @Const @ByRef TensorShape shape();

  /** \brief Convenience accessor for the tensor shape.
   * 
   *  For all shape accessors, see comments for relevant methods of
   *  {@code TensorShape} in {@code tensor_shape.h}. */
  public native int dims();

  /** Convenience accessor for the tensor shape. */
  public native @Cast("tensorflow::int64") long dim_size(int d);

  /** Convenience accessor for the tensor shape. */
  public native @Cast("tensorflow::int64") long NumElements();

  public native @Cast("bool") boolean IsSameSize(@Const @ByRef Tensor b);

  // True iff the two tensors use the same underlying refcounted storage
  
  ///
  public native @Cast("bool") boolean SharesBufferWith(@Const @ByRef Tensor b);

  /** \brief If necessary, has this Tensor been initialized?
   * 
   *  Zero-element Tensors are always considered initialized, even if they
   *  have never been assigned to and do not have any memory allocated. */
  public native @Cast("bool") boolean IsInitialized();

  /** Returns the estimated memory usage of this tensor. */
  public native @Cast("size_t") long TotalBytes();

  // Returns the size of allocated memory for this tensor.
  public native @Cast("size_t") long AllocatedBytes();

  /** Returns true iff this tensor is aligned. */
  public native @Cast("bool") boolean IsAligned();

  /** Assign operator. This tensor shares other's underlying storage. */
  public native @ByRef @Name("operator =") Tensor put(@Const @ByRef Tensor other);

  /** Move operator.  See move constructor for details. */

  /** \brief Copy the other tensor into this tensor and reshape it.
   * 
   *  This tensor shares other's underlying storage. Returns {@code true}
   *  iff {@code other.shape()} has the same number of elements of the given
   *  {@code shape}. */
  
  ///
  ///
  ///
  public native @Cast("bool") boolean CopyFrom(@Const @ByRef Tensor other,
                  @Const @ByRef TensorShape shape);

  /** \brief Slice this tensor along the 1st dimension.
   <p>
   *  I.e., the returned tensor satisfies
   *      returned[i, ...] == this[dim0_start + i, ...].
   *  The returned tensor shares the underlying tensor buffer with this
   *  tensor.
   * 
   *  NOTE: The returned tensor may not satisfy the same alignment
   *  requirement as this tensor depending on the shape. The caller
   *  must check the returned tensor's alignment before calling certain
   *  methods that have alignment requirement (e.g., {@code flat()}, {@code tensor()}).
   * 
   *  NOTE: When fed with an N-dimensional tensor, this method returns a tensor
   *  also with N dimensions. If you want to select a sub tensor, see SubSlice.
   * 
   *  REQUIRES: {@code dims()} >= 1
   *  REQUIRES: {@code 0 <= dim0_start <= dim0_limit <= dim_size(0)} */
  
  ///
  ///
  ///
  public native @ByVal Tensor Slice(@Cast("tensorflow::int64") long dim0_start, @Cast("tensorflow::int64") long dim0_limit);

  /** \brief Select a subslice from this tensor along the 1st dimension.
   * 
   *  When fed with an N-dimensional tensor, this method returns a tensor with
   *  N-1 dimensions, where the returned tensor is a subslice of the input
   *  tensor along the first dimension. The N-1 dimensions of the returned
   *  tensor are the last N-1 dimensions of the input tensor.
   * 
   *  NOTE: The returned tensor may not satisfy the same alignment
   *  requirement as this tensor depending on the shape. The caller
   *  must check the returned tensor's alignment before calling certain
   *  methods that have alignment requirement (e.g., {@code flat()}, {@code tensor()}).
   * 
   *  REQUIRES: {@code dims()} >= 1
   *  REQUIRES: {@code 0 <= dim0_start < dim_size(0)} */
  public native @ByVal Tensor SubSlice(@Cast("tensorflow::int64") long index);

  /** \brief Parse {@code other} and construct the tensor.
   <p>
   *  Returns {@code true} iff the parsing succeeds. If the parsing fails,
   *  the state of {@code *this} is unchanged. */
  public native @Cast("bool") boolean FromProto(@Const @ByRef TensorProto other);
  
  ///
  public native @Cast("bool") boolean FromProto(Allocator a, @Const @ByRef TensorProto other);

  /** \brief Fills in {@code proto} with {@code *this} tensor's content.
   * 
   *  {@code AsProtoField()} fills in the repeated field for {@code proto.dtype()}, while
   *  {@code AsProtoTensorContent()} encodes the content in {@code proto.tensor_content()}
   *  in a compact form. */
  public native void AsProtoField(TensorProto proto);
  
  ///
  ///
  ///
  ///
  ///
  public native void AsProtoTensorContent(TensorProto proto);

  /** \brief Return the tensor data as an {@code Eigen::Tensor} with the type and
   *  sizes of this {@code Tensor}.
   * 
   *  Use these methods when you know the data type and the number of
   *  dimensions of the Tensor and you want an {@code Eigen::Tensor}
   *  automatically sized to the {@code Tensor} sizes. The implementation check
   *  fails if either type or sizes mismatch.
   * 
   *  Example:
   * 
   *  <pre>{@code c++
   * 
   *      typedef float T;
   *      Tensor my_mat(...built with Shape{rows: 3, cols: 5}...);
   *      auto mat = my_mat.matrix<T>();    // 2D Eigen::Tensor, 3 x 5.
   *      auto mat = my_mat.tensor<T, 2>(); // 2D Eigen::Tensor, 3 x 5.
   *      auto vec = my_mat.vec<T>();       // CHECK fails as my_mat is 2D.
   *      auto vec = my_mat.tensor<T, 3>(); // CHECK fails as my_mat is 2D.
   *      auto mat = my_mat.matrix<int32>();// CHECK fails as type mismatch.
   * 
   *  }</pre> */

  /** \brief Return the tensor data to an {@code Eigen::Tensor} with the
   *  same size but a bitwise cast to the specified dtype {@code T}.
   * 
   *  Using a bitcast is useful for move and copy operations.
   *  NOTE: this is the same as {@code tensor()} except a bitcast is allowed. */

  /** \brief Return the tensor data to an {@code Eigen::Tensor} with the
   *  last dimension elements converted into single elements of a larger type.
   * 
   *  For example, this is useful for kernels that can treat NCHW_VECT_C int8
   *  tensors as NCHW int32 tensors. The sizeof(T) should equal the size of
   *  the original element type * num elements in the original last dimension.
   *  NDIMS should be 1 less than the original number of dimensions. */

  /** \brief Return the tensor data as an {@code Eigen::Tensor} of the data type and a
   *  specified shape.
   * 
   *  These methods allow you to access the data with the dimensions
   *  and sizes of your choice.  You do not need to know the number of
   *  dimensions of the Tensor to call them.  However, they {@code CHECK} that
   *  the type matches and the dimensions requested creates an
   *  {@code Eigen::Tensor} with the same number of elements as the tensor.
   * 
   *  Example:
   * 
   *  <pre>{@code c++
   * 
   *      typedef float T;
   *      Tensor my_ten(...built with Shape{planes: 4, rows: 3, cols: 5}...);
   *      // 1D Eigen::Tensor, size 60:
   *      auto flat = my_ten.flat<T>();
   *      // 2D Eigen::Tensor 12 x 5:
   *      auto inner = my_ten.flat_inner_dims<T>();
   *      // 2D Eigen::Tensor 4 x 15:
   *      auto outer = my_ten.shaped<T, 2>({4, 15});
   *      // CHECK fails, bad num elements:
   *      auto outer = my_ten.shaped<T, 2>({4, 8});
   *      // 3D Eigen::Tensor 6 x 5 x 2:
   *      auto weird = my_ten.shaped<T, 3>({6, 5, 2});
   *      // CHECK fails, type mismatch:
   *      auto bad   = my_ten.flat<int32>();
   * 
   *  }</pre> */

  /** Returns the data as an Eigen::Tensor with NDIMS dimensions, collapsing all
   *  Tensor dimensions but the last NDIMS-1 into the first dimension of the
   *  result. If NDIMS > dims() then leading dimensions of size 1 will be
   *  added to make the output rank NDIMS. */

  /** Returns the data as an Eigen::Tensor with NDIMS dimensions, collapsing all
   *  Tensor dimensions but the first NDIMS-1 into the last dimension of the
   *  result. If NDIMS > dims() then trailing dimensions of size 1 will be
   *  added to make the output rank NDIMS. */

  /** Returns the data as an Eigen::Tensor with NDIMS dimensions, collapsing the
   *  first 'begin' Tensor dimensions into the first dimension of the result and
   *  the Tensor dimensions of the last dims() - 'begin' - NDIMS into the last
   *  dimension of the result. If 'begin' < 0 then the |'begin'| leading
   *  dimensions of size 1 will be added. If 'begin' + NDIMS > dims() then
   *  'begin' + NDIMS - dims() trailing dimensions of size 1 will be added. */

  /** \brief Return the tensor data to an {@code Eigen::Tensor} with the new
   *  shape specified in {@code new_sizes} and cast to a new dtype {@code T}.
   * 
   *  Using a bitcast is useful for move and copy operations.
   *  The allowed bitcast is the only difference from {@code shaped()}. */

  /** \brief Return the Tensor data as a {@code TensorMap} of fixed size 1:
   *  {@code TensorMap<TensorFixedSize<T, 1>>}.
   <p>
   *  Using {@code scalar()} allows the compiler to perform optimizations as
   *  the size of the tensor is known at compile time. */

  /** Const versions of all the methods above. */

  /** \brief Return the tensor data to an {@code Eigen::Tensor} with the
   *  same size but a bitwise cast to the specified dtype {@code T}.
   * 
   *  Using a bitcast is useful for move and copy operations.
   *  NOTE: this is the same as {@code tensor()} except a bitcast is allowed. */

  /** \brief Return the tensor data to an {@code Eigen::Tensor} with the
   *  last dimension elements converted into single elements of a larger type.
   * 
   *  For example, this is useful for kernels that can treat NCHW_VECT_C int8
   *  tensors as NCHW int32 tensors. The sizeof(T) should equal the size of
   *  the original element type * num elements in the original last dimension.
   *  NDIMS should be 1 less than the original number of dimensions. */

  /** \brief Return the tensor data to an {@code Eigen::Tensor} with the new
   *  shape specified in {@code new_sizes} and cast to a new dtype {@code T}.
   * 
   *  Using a bitcast is useful for move and copy operations.
   *  The allowed bitcast is the only difference from {@code shaped()}. */

  /** Render the first {@code max_entries} values in {@code *this} into a string. */
  public native @StdString BytePointer SummarizeValue(@Cast("tensorflow::int64") long max_entries, @Cast("bool") boolean print_v2/*=false*/);
  public native @StdString BytePointer SummarizeValue(@Cast("tensorflow::int64") long max_entries);

  /** A human-readable summary of the tensor suitable for debugging. */
  // `num_values` is the number of actual data values in the tensor
  // included in the message. If the tensor might be resident in
  // GPU/TPU memory use DeviceSafeDebugString instead.
  public native @StdString BytePointer DebugString(int num_values);
  public native @StdString BytePointer DebugString();

  // Variant of DebugString() that should be used for possibly non-CPU tensors.
  // If the tensor is not resident on CPU, we can't read its values as
  // DebugString() does.
  public native @StdString BytePointer DeviceSafeDebugString();

  /** Fill in the {@code TensorDescription} proto with metadata about the
   *  tensor that is useful for monitoring and debugging. */
  
  ///
  ///
  ///
  public native void FillDescription(TensorDescription description);

  /** \brief Returns a {@code StringPiece} mapping the current tensor's buffer.
   * 
   *  The returned {@code StringPiece} may point to memory location on devices
   *  that the CPU cannot address directly.
   * 
   *  NOTE: The underlying tensor buffer is refcounted, so the lifetime
   *  of the contents mapped by the {@code StringPiece} matches the lifetime of
   *  the buffer; callers should arrange to make sure the buffer does
   *  not get destroyed while the {@code StringPiece} is still used.
   * 
   *  REQUIRES: {@code DataTypeCanUseMemcpy(dtype())}. */
  
  ///
  ///
  ///
  ///
  ///
  ///
  ///
  public native @StringPiece BytePointer tensor_data();

  /** Copy the other tensor into this tensor, reshape it and reinterpret the
   *  buffer's datatype. If Status::OK() is returned, the two tensors now share
   *  the same underlying storage.
   * 
   *  This call requires that the {@code other} tensor and the given type and shape
   *  are "compatible" (i.e. they occupy the same number of bytes).
   * 
   *  Specifically:
   * 
   *  shape.num_elements() * DataTypeSize(type)
   * 
   *  must equal
   * 
   *  other.num_elements() * DataTypeSize(other.dtype())
   * 
   *  In addition, this function requires:
   *    * DataTypeSize(other.dtype()) != 0
   *    * DataTypeSize(type) != 0
   * 
   *  If any of the requirements are not met, errors::InvalidArgument is
   *  returned. */
  
  ///
  public native @ByVal Status BitcastFrom(@Const @ByRef Tensor other, @Cast("tensorflow::DataType") int dtype,
                       @Const @ByRef TensorShape shape);

  /** Like BitcastFrom, but CHECK fails if any preconditions are not met.
   * 
   *  Deprecated. Use BitcastFrom instead and check the returned Status. */
  public native void UnsafeCopyFromInternal(@Const @ByRef Tensor other, @Cast("tensorflow::DataType") int dtype,
                                @Const @ByRef TensorShape shape);
}
