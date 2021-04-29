// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.tensorrt.nvinfer;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.cuda.cudart.*;
import static org.bytedeco.cuda.global.cudart.*;
import org.bytedeco.cuda.cublas.*;
import static org.bytedeco.cuda.global.cublas.*;
import org.bytedeco.cuda.cudnn.*;
import static org.bytedeco.cuda.global.cudnn.*;
import org.bytedeco.cuda.nvrtc.*;
import static org.bytedeco.cuda.global.nvrtc.*;

import static org.bytedeco.tensorrt.global.nvinfer.*;


/**
 *  Helper for creating a recurrent subgraph.
 *  */
@Namespace("nvinfer1") @Properties(inherit = org.bytedeco.tensorrt.presets.nvinfer.class)
public class ILoop extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public ILoop(Pointer p) { super(p); }

    /**
     *  \brief Create a recurrence layer for this loop with initialValue as its first input.
     * 
     *  IRecurrenceLayer requires exactly two inputs.  The 2nd input must be added, via method IRecurrenceLayer::setInput(1,...)
     *  before an Engine can be built. */
    //
    /** */
    
    
    //!
    //!
    //!
    //!
    //!
    public native @NoException IRecurrenceLayer addRecurrence(@ByRef ITensor initialValue);

    /**
     *  \brief Add a trip-count limiter, based on the given tensor.
     * 
     *  There may be at most one kCOUNT and one kWHILE limiter for a loop.
     *  When both trip limits exist, the loop exits when the
     *  count is reached or condition is falsified.
     *  It is an error to not add at least one trip limiter.
     * 
     *  For kTRIP_LIMIT, the input tensor must be available before the loop starts.
     * 
     *  For kWHILE, the input tensor must be the output of a subgraph that contains
     *  only layers that are not ITripLimitLayer, IIteratorLayer or ILoopOutputLayer.
     *  Any IRecurrenceLayers in the subgraph must belong to the same loop as the
     *  ITripLimitLayer.  A trivial example of this rule is that the input to the kWHILE
     *  is the output of an IRecurrenceLayer for the same loop.
     *  */
    
    
    //!
    //!
    //!
    public native @NoException ITripLimitLayer addTripLimit(@ByRef ITensor tensor, TripLimit _limit);
    public native @NoException ITripLimitLayer addTripLimit(@ByRef ITensor tensor, @Cast("nvinfer1::TripLimit") int _limit);

    /**
     *  \brief Return layer that subscripts tensor by loop iteration.
     * 
     *  For reverse=false, this is equivalent to addGather(tensor, I, 0) where I is a
     *  scalar tensor containing the loop iteration number.
     *  For reverse=true, this is equivalent to addGather(tensor, M-1-I, 0) where M is the trip count
     *  computed from TripLimits of kind kCOUNT.
     *  */
    
    //!
    //!
    //!
    public native @NoException IIteratorLayer addIterator(@ByRef ITensor tensor, int axis/*=0*/, @Cast("bool") boolean reverse/*=false*/);
    public native @NoException IIteratorLayer addIterator(@ByRef ITensor tensor);

    /** \brief Make an output for this loop, based on the given tensor.
     * 
     *  axis is the axis for concatenation (if using outputKind of kCONCATENATE or kREVERSE).
     * 
     *  If outputKind is kCONCATENATE or kREVERSE, a second input specifying the
     *  concatenation dimension must be added via method ILoopOutputLayer::setInput.
     *  */
    
    
    //!
    //!
    //!
    //!
    public native @NoException ILoopOutputLayer addLoopOutput(@ByRef ITensor tensor, LoopOutput outputKind, int axis/*=0*/);
    public native @NoException ILoopOutputLayer addLoopOutput(@ByRef ITensor tensor, LoopOutput outputKind);
    public native @NoException ILoopOutputLayer addLoopOutput(@ByRef ITensor tensor, @Cast("nvinfer1::LoopOutput") int outputKind, int axis/*=0*/);
    public native @NoException ILoopOutputLayer addLoopOutput(@ByRef ITensor tensor, @Cast("nvinfer1::LoopOutput") int outputKind);

    /**
     *  \brief Set the name of the loop.
     * 
     *  The name is used in error diagnostics.
     *  This method copies the name string.
     * 
     *  @see getName()
     *  */
    
    
    //!
    //!
    //!
    public native @NoException void setName(String name);
    public native @NoException void setName(@Cast("const char*") BytePointer name);

    /**
     *  \brief Return the name of the loop.
     * 
     *  @see setName()
     *  */
    public native @NoException String getName();
}
