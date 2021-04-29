// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cpython;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.cpython.global.python.*;


/* Py_False and Py_True are the only two bools in existence.
Don't forget to apply Py_INCREF() when returning either!!! */

/* Don't use these directly */
@Opaque @Properties(inherit = org.bytedeco.cpython.presets.python.class)
public class _Py_FalseStruct extends Pointer {
    /** Empty constructor. Calls {@code super((Pointer)null)}. */
    public _Py_FalseStruct() { super((Pointer)null); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public _Py_FalseStruct(Pointer p) { super(p); }
}
