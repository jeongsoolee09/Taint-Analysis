// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.tensorrt.nvonnxparser;

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
import org.bytedeco.tensorrt.nvinfer.*;
import static org.bytedeco.tensorrt.global.nvinfer.*;
import org.bytedeco.tensorrt.nvinfer_plugin.*;
import static org.bytedeco.tensorrt.global.nvinfer_plugin.*;

import static org.bytedeco.tensorrt.global.nvonnxparser.*;


/** \class IParserError
 *
 * \brief an object containing information about an error
 */
@Namespace("nvonnxparser") @Properties(inherit = org.bytedeco.tensorrt.presets.nvonnxparser.class)
public class IParserError extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public IParserError(Pointer p) { super(p); }

    /** \brief the error code
     */
    public native org.bytedeco.tensorrt.global.nvonnxparser.ErrorCode code();
    /** \brief description of the error
     */
    public native String desc();
    /** \brief source file in which the error occurred
     */
    public native String file();
    /** \brief source line at which the error occurred
     */
    public native int line();
    /** \brief source function in which the error occurred
     */
    public native String func();
    /** \brief index of the ONNX model node in which the error occurred
     */
    public native int node();
}
