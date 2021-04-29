// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.arrow;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.arrow.global.arrow.*;


/** \class BinaryBuilder
 *  \brief Builder class for variable-length binary data */
@Namespace("arrow") @Properties(inherit = org.bytedeco.arrow.presets.arrow.class)
public class BinaryBuilder extends BaseBinaryBuilder {
    static { Loader.load(); }

  
  
    public BinaryBuilder(MemoryPool pool/*=arrow::default_memory_pool()*/) { super((Pointer)null); allocate(pool); }
    private native void allocate(MemoryPool pool/*=arrow::default_memory_pool()*/);
    public BinaryBuilder() { super((Pointer)null); allocate(); }
    private native void allocate();
  
    public BinaryBuilder(@SharedPtr @Cast({"", "std::shared_ptr<arrow::DataType>"}) DataType type, MemoryPool pool) { super((Pointer)null); allocate(type, pool); }
    private native void allocate(@SharedPtr @Cast({"", "std::shared_ptr<arrow::DataType>"}) DataType type, MemoryPool pool);
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public BinaryBuilder(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public BinaryBuilder(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public BinaryBuilder position(long position) {
        return (BinaryBuilder)super.position(position);
    }
    @Override public BinaryBuilder getPointer(long i) {
        return new BinaryBuilder((Pointer)this).position(position + i);
    }


  /** \cond FALSE */
  /** \endcond */

  public native @ByVal Status Finish(@SharedPtr BinaryArray out);

  public native @SharedPtr @Cast({"", "std::shared_ptr<arrow::DataType>"}) DataType type();
}
