// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.hdf5;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.hdf5.global.hdf5.*;


/* The H5L_class_t struct can be used to override the behavior of a
 * "user-defined" link class. Users should populate the struct with callback
 * functions defined below.
 */
/* Callback prototypes for user-defined links */
/* Link creation callback */
@Properties(inherit = org.bytedeco.hdf5.presets.hdf5.class)
public class H5L_create_func_t extends FunctionPointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public    H5L_create_func_t(Pointer p) { super(p); }
    protected H5L_create_func_t() { allocate(); }
    private native void allocate();
    public native @Cast("herr_t") int call(@Cast("const char*") BytePointer link_name, @Cast("hid_t") long loc_group,
    @Const Pointer lnkdata, @Cast("size_t") long lnkdata_size, @Cast("hid_t") long lcpl_id);
}