// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.cpython;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

import static org.bytedeco.cpython.global.python.*;

/* End buffer interface */


@Properties(inherit = org.bytedeco.cpython.presets.python.class)
public class PyNumberMethods extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public PyNumberMethods() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public PyNumberMethods(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public PyNumberMethods(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public PyNumberMethods position(long position) {
        return (PyNumberMethods)super.position(position);
    }
    @Override public PyNumberMethods getPointer(long i) {
        return new PyNumberMethods((Pointer)this).position(position + i);
    }

    /* Number implementations must check *both*
       arguments for proper type and implement the necessary conversions
       in the slot functions themselves. */

    public native binaryfunc nb_add(); public native PyNumberMethods nb_add(binaryfunc setter);
    public native binaryfunc nb_subtract(); public native PyNumberMethods nb_subtract(binaryfunc setter);
    public native binaryfunc nb_multiply(); public native PyNumberMethods nb_multiply(binaryfunc setter);
    public native binaryfunc nb_remainder(); public native PyNumberMethods nb_remainder(binaryfunc setter);
    public native binaryfunc nb_divmod(); public native PyNumberMethods nb_divmod(binaryfunc setter);
    public native ternaryfunc nb_power(); public native PyNumberMethods nb_power(ternaryfunc setter);
    public native unaryfunc nb_negative(); public native PyNumberMethods nb_negative(unaryfunc setter);
    public native unaryfunc nb_positive(); public native PyNumberMethods nb_positive(unaryfunc setter);
    public native unaryfunc nb_absolute(); public native PyNumberMethods nb_absolute(unaryfunc setter);
    public native inquiry nb_bool(); public native PyNumberMethods nb_bool(inquiry setter);
    public native unaryfunc nb_invert(); public native PyNumberMethods nb_invert(unaryfunc setter);
    public native binaryfunc nb_lshift(); public native PyNumberMethods nb_lshift(binaryfunc setter);
    public native binaryfunc nb_rshift(); public native PyNumberMethods nb_rshift(binaryfunc setter);
    public native binaryfunc nb_and(); public native PyNumberMethods nb_and(binaryfunc setter);
    public native binaryfunc nb_xor(); public native PyNumberMethods nb_xor(binaryfunc setter);
    public native binaryfunc nb_or(); public native PyNumberMethods nb_or(binaryfunc setter);
    public native unaryfunc nb_int(); public native PyNumberMethods nb_int(unaryfunc setter);
    public native Pointer nb_reserved(); public native PyNumberMethods nb_reserved(Pointer setter);  /* the slot formerly known as nb_long */
    public native unaryfunc nb_float(); public native PyNumberMethods nb_float(unaryfunc setter);

    public native binaryfunc nb_inplace_add(); public native PyNumberMethods nb_inplace_add(binaryfunc setter);
    public native binaryfunc nb_inplace_subtract(); public native PyNumberMethods nb_inplace_subtract(binaryfunc setter);
    public native binaryfunc nb_inplace_multiply(); public native PyNumberMethods nb_inplace_multiply(binaryfunc setter);
    public native binaryfunc nb_inplace_remainder(); public native PyNumberMethods nb_inplace_remainder(binaryfunc setter);
    public native ternaryfunc nb_inplace_power(); public native PyNumberMethods nb_inplace_power(ternaryfunc setter);
    public native binaryfunc nb_inplace_lshift(); public native PyNumberMethods nb_inplace_lshift(binaryfunc setter);
    public native binaryfunc nb_inplace_rshift(); public native PyNumberMethods nb_inplace_rshift(binaryfunc setter);
    public native binaryfunc nb_inplace_and(); public native PyNumberMethods nb_inplace_and(binaryfunc setter);
    public native binaryfunc nb_inplace_xor(); public native PyNumberMethods nb_inplace_xor(binaryfunc setter);
    public native binaryfunc nb_inplace_or(); public native PyNumberMethods nb_inplace_or(binaryfunc setter);

    public native binaryfunc nb_floor_divide(); public native PyNumberMethods nb_floor_divide(binaryfunc setter);
    public native binaryfunc nb_true_divide(); public native PyNumberMethods nb_true_divide(binaryfunc setter);
    public native binaryfunc nb_inplace_floor_divide(); public native PyNumberMethods nb_inplace_floor_divide(binaryfunc setter);
    public native binaryfunc nb_inplace_true_divide(); public native PyNumberMethods nb_inplace_true_divide(binaryfunc setter);

    public native unaryfunc nb_index(); public native PyNumberMethods nb_index(unaryfunc setter);

    public native binaryfunc nb_matrix_multiply(); public native PyNumberMethods nb_matrix_multiply(binaryfunc setter);
    public native binaryfunc nb_inplace_matrix_multiply(); public native PyNumberMethods nb_inplace_matrix_multiply(binaryfunc setter);
}
