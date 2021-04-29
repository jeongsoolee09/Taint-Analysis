// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.hdf5;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.hdf5.global.hdf5.*;


/* Prototype for H5Ovisit/H5Ovisit_by_name() operator (version 3) */
@Properties(inherit = org.bytedeco.hdf5.presets.hdf5.class)
public class H5O_iterate2_t extends FunctionPointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public    H5O_iterate2_t(Pointer p) { super(p); }
    protected H5O_iterate2_t() { allocate(); }
    private native void allocate();
    public native @Cast("herr_t") int call(@Cast("hid_t") long obj, @Cast("const char*") BytePointer name, @Const H5O_info2_t info,
    Pointer op_data);
}
