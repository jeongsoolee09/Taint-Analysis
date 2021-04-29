// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.parquet;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.arrow.*;
import static org.bytedeco.arrow.global.arrow.*;

import static org.bytedeco.arrow.global.parquet.*;


@Name("parquet::type_traits<parquet::Type::BOOLEAN>") @Properties(inherit = org.bytedeco.arrow.presets.parquet.class)
public class type_traits extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public type_traits() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public type_traits(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public type_traits(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public type_traits position(long position) {
        return (type_traits)super.position(position);
    }
    @Override public type_traits getPointer(long i) {
        return new type_traits((Pointer)this).position(position + i);
    }


  @MemberGetter public static native int value_byte_size();
  public static final int value_byte_size = value_byte_size();
  @MemberGetter public static native String printf_code();
}