// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.arrow;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.arrow.global.arrow.*;


@Namespace("arrow") @Properties(inherit = org.bytedeco.arrow.presets.arrow.class)
public class DictionaryScalar extends Scalar {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public DictionaryScalar(Pointer p) { super(p); }


  public DictionaryScalar(@SharedPtr @Cast({"", "std::shared_ptr<arrow::DataType>"}) DataType type) { super((Pointer)null); allocate(type); }
  private native void allocate(@SharedPtr @Cast({"", "std::shared_ptr<arrow::DataType>"}) DataType type);

  public DictionaryScalar(@ByVal @Cast("arrow::DictionaryScalar::ValueType*") Pointer value, @SharedPtr @Cast({"", "std::shared_ptr<arrow::DataType>"}) DataType type, @Cast("bool") boolean is_valid/*=true*/) { super((Pointer)null); allocate(value, type, is_valid); }
  private native void allocate(@ByVal @Cast("arrow::DictionaryScalar::ValueType*") Pointer value, @SharedPtr @Cast({"", "std::shared_ptr<arrow::DataType>"}) DataType type, @Cast("bool") boolean is_valid/*=true*/);
  public DictionaryScalar(@ByVal @Cast("arrow::DictionaryScalar::ValueType*") Pointer value, @SharedPtr @Cast({"", "std::shared_ptr<arrow::DataType>"}) DataType type) { super((Pointer)null); allocate(value, type); }
  private native void allocate(@ByVal @Cast("arrow::DictionaryScalar::ValueType*") Pointer value, @SharedPtr @Cast({"", "std::shared_ptr<arrow::DataType>"}) DataType type);

  public native @ByVal ScalarResult GetEncodedValue();
}
