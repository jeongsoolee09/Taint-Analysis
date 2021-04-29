// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.gsl;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import static org.bytedeco.openblas.global.openblas_nolapack.*;
import static org.bytedeco.openblas.global.openblas.*;

import static org.bytedeco.gsl.global.gsl.*;


@Properties(inherit = org.bytedeco.gsl.presets.gsl.class)
public class gsl_multifit_fdfsolver extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public gsl_multifit_fdfsolver() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public gsl_multifit_fdfsolver(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public gsl_multifit_fdfsolver(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public gsl_multifit_fdfsolver position(long position) {
        return (gsl_multifit_fdfsolver)super.position(position);
    }
    @Override public gsl_multifit_fdfsolver getPointer(long i) {
        return new gsl_multifit_fdfsolver(this).position(position + i);
    }

    public native @Const gsl_multifit_fdfsolver_type type(); public native gsl_multifit_fdfsolver type(gsl_multifit_fdfsolver_type setter);
    public native gsl_multifit_function_fdf fdf(); public native gsl_multifit_fdfsolver fdf(gsl_multifit_function_fdf setter);
    public native gsl_vector x(); public native gsl_multifit_fdfsolver x(gsl_vector setter);        /* parameter values x */
    public native gsl_vector f(); public native gsl_multifit_fdfsolver f(gsl_vector setter);        /* residual vector f(x) */
    public native gsl_vector dx(); public native gsl_multifit_fdfsolver dx(gsl_vector setter);       /* step dx */
    public native gsl_vector g(); public native gsl_multifit_fdfsolver g(gsl_vector setter);        /* gradient J^T f */
    public native gsl_vector sqrt_wts(); public native gsl_multifit_fdfsolver sqrt_wts(gsl_vector setter); /* sqrt(wts) */
    public native @Cast("size_t") long niter(); public native gsl_multifit_fdfsolver niter(long setter);          /* number of iterations performed */
    public native Pointer state(); public native gsl_multifit_fdfsolver state(Pointer setter);
  }
