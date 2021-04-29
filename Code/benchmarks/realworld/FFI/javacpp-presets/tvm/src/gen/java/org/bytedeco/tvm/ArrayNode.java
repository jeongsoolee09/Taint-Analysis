// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.tvm;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.dnnl.*;
import static org.bytedeco.dnnl.global.dnnl.*;
import org.bytedeco.llvm.LLVM.*;
import static org.bytedeco.llvm.global.LLVM.*;
import static org.bytedeco.mkl.global.mkl_rt.*;

import static org.bytedeco.tvm.global.tvm_runtime.*;


/** \brief array node content in array */
@Namespace("tvm::runtime") @NoOffset @Properties(inherit = org.bytedeco.tvm.presets.tvm_runtime.class)
public class ArrayNode extends TVMObject {
    static { Loader.load(); }
    /** Default native constructor. */
    public ArrayNode() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public ArrayNode(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public ArrayNode(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public ArrayNode position(long position) {
        return (ArrayNode)super.position(position);
    }
    @Override public ArrayNode getPointer(long i) {
        return new ArrayNode(this).position(position + i);
    }
    public ArrayNodeBase asArrayNodeBase() { return asArrayNodeBase(this); }
    @Namespace public static native @Name("static_cast<tvm::runtime::InplaceArrayBase<tvm::runtime::ArrayNode,tvm::runtime::ObjectRef>*>") ArrayNodeBase asArrayNodeBase(ArrayNode pointer);

  /** @return The size of the array */
  public native @Cast("size_t") long size();

  /**
   * \brief Read i-th element from array.
   * @param i The index
   * @return the i-th element.
   */
  public native @Const @ByVal ObjectRef at(@Cast("int64_t") long i);

  /** @return begin constant iterator */
  public native @Const ObjectRef begin();

  /** @return end constant iterator */
  public native @Const ObjectRef end();

  /** \brief Release reference to all the elements */
  public native void clear();

  /**
   * \brief Set i-th element of the array in-place
   * @param i The index
   * @param item The value to be set
   */
  public native void SetItem(@Cast("int64_t") long i, @ByVal ObjectRef item);

  /**
   * \brief Constructs a container and copy from another
   * @param cap The capacity of the container
   * @param from Source of the copy
   * @return Ref-counted ArrayNode requested
   */
  public static native @ByVal ArrayNodePtr CopyFrom(@Cast("int64_t") long cap, ArrayNode from);

  /**
   * \brief Constructs a container and move from another
   * @param cap The capacity of the container
   * @param from Source of the move
   * @return Ref-counted ArrayNode requested
   */
  public static native @ByVal ArrayNodePtr MoveFrom(@Cast("int64_t") long cap, ArrayNode from);

  /**
   * \brief Constructs a container with n elements. Each element is a copy of val
   * @param n The size of the container
   * @param val The init value
   * @return Ref-counted ArrayNode requested
   */
  public static native @ByVal ArrayNodePtr CreateRepeated(@Cast("int64_t") long n, @Const @ByRef ObjectRef val);

  @MemberGetter public static native @Cast("const uint32_t") int _type_index();
  public static final int _type_index = _type_index();
  @MemberGetter public static native @Cast("const char*") BytePointer _type_key();
  @MemberGetter public static native @Cast("const bool") boolean _type_final();
  public static final boolean _type_final = _type_final();
  @MemberGetter public static native int _type_child_slots();
  public static final int _type_child_slots = _type_child_slots();
  public static native @Cast("uint32_t") int RuntimeTypeIndex();
  public static native @Cast("uint32_t") int _GetOrAllocRuntimeTypeIndex();
}
