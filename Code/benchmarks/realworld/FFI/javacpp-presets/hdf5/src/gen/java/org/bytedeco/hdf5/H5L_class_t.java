// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.hdf5;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.hdf5.global.hdf5.*;


@Properties(inherit = org.bytedeco.hdf5.presets.hdf5.class)
public class H5L_class_t extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public H5L_class_t() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public H5L_class_t(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public H5L_class_t(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public H5L_class_t position(long position) {
        return (H5L_class_t)super.position(position);
    }
    @Override public H5L_class_t getPointer(long i) {
        return new H5L_class_t(this).position(position + i);
    }

    public native int version(); public native H5L_class_t version(int setter);                    /* Version number of this struct        */
    public native @Cast("H5L_type_t") int id(); public native H5L_class_t id(int setter);                  /* Link type ID                         */
    public native @Cast("const char*") BytePointer comment(); public native H5L_class_t comment(BytePointer setter);            /* Comment for debugging                */
    public native H5L_create_func_t create_func(); public native H5L_class_t create_func(H5L_create_func_t setter);  /* Callback during link creation        */
    public native H5L_move_func_t move_func(); public native H5L_class_t move_func(H5L_move_func_t setter);      /* Callback after moving link           */
    public native H5L_copy_func_t copy_func(); public native H5L_class_t copy_func(H5L_copy_func_t setter);      /* Callback after copying link          */
    public native H5L_traverse_func_t trav_func(); public native H5L_class_t trav_func(H5L_traverse_func_t setter);  /* Callback during link traversal       */
    public native H5L_delete_func_t del_func(); public native H5L_class_t del_func(H5L_delete_func_t setter);     /* Callback for link deletion           */
    public native H5L_query_func_t query_func(); public native H5L_class_t query_func(H5L_query_func_t setter);    /* Callback for queries                 */
}
