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
public class gsl_monte_vegas_state extends Pointer {
    static { Loader.load(); }
    /** Default native constructor. */
    public gsl_monte_vegas_state() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public gsl_monte_vegas_state(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public gsl_monte_vegas_state(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public gsl_monte_vegas_state position(long position) {
        return (gsl_monte_vegas_state)super.position(position);
    }
    @Override public gsl_monte_vegas_state getPointer(long i) {
        return new gsl_monte_vegas_state(this).position(position + i);
    }

  /* grid */
  public native @Cast("size_t") long dim(); public native gsl_monte_vegas_state dim(long setter);
  public native @Cast("size_t") long bins_max(); public native gsl_monte_vegas_state bins_max(long setter);
  public native @Cast("unsigned int") int bins(); public native gsl_monte_vegas_state bins(int setter);
  public native @Cast("unsigned int") int boxes(); public native gsl_monte_vegas_state boxes(int setter); /* these are both counted along the axes */
  public native DoublePointer xi(); public native gsl_monte_vegas_state xi(DoublePointer setter);
  public native DoublePointer xin(); public native gsl_monte_vegas_state xin(DoublePointer setter);
  public native DoublePointer delx(); public native gsl_monte_vegas_state delx(DoublePointer setter);
  public native DoublePointer weight(); public native gsl_monte_vegas_state weight(DoublePointer setter);
  public native double vol(); public native gsl_monte_vegas_state vol(double setter);

  public native DoublePointer x(); public native gsl_monte_vegas_state x(DoublePointer setter);
  public native IntPointer bin(); public native gsl_monte_vegas_state bin(IntPointer setter);
  public native IntPointer box(); public native gsl_monte_vegas_state box(IntPointer setter);
  
  /* distribution */
  public native DoublePointer d(); public native gsl_monte_vegas_state d(DoublePointer setter);

  /* control variables */
  public native double alpha(); public native gsl_monte_vegas_state alpha(double setter);
  public native int mode(); public native gsl_monte_vegas_state mode(int setter);
  public native int verbose(); public native gsl_monte_vegas_state verbose(int setter);
  public native @Cast("unsigned int") int iterations(); public native gsl_monte_vegas_state iterations(int setter);
  public native int stage(); public native gsl_monte_vegas_state stage(int setter);

  /* scratch variables preserved between calls to vegas1/2/3  */
  public native double jac(); public native gsl_monte_vegas_state jac(double setter);
  public native double wtd_int_sum(); public native gsl_monte_vegas_state wtd_int_sum(double setter); 
  public native double sum_wgts(); public native gsl_monte_vegas_state sum_wgts(double setter);
  public native double chi_sum(); public native gsl_monte_vegas_state chi_sum(double setter);
  public native double chisq(); public native gsl_monte_vegas_state chisq(double setter);

  public native double result(); public native gsl_monte_vegas_state result(double setter);
  public native double sigma(); public native gsl_monte_vegas_state sigma(double setter);

  public native @Cast("unsigned int") int it_start(); public native gsl_monte_vegas_state it_start(int setter);
  public native @Cast("unsigned int") int it_num(); public native gsl_monte_vegas_state it_num(int setter);
  public native @Cast("unsigned int") int samples(); public native gsl_monte_vegas_state samples(int setter);
  public native @Cast("unsigned int") int calls_per_box(); public native gsl_monte_vegas_state calls_per_box(int setter);

  public native FILE ostream(); public native gsl_monte_vegas_state ostream(FILE setter);

}