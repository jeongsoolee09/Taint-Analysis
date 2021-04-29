// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.dnnl;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import org.bytedeco.opencl.*;
import static org.bytedeco.opencl.global.OpenCL.*;

import static org.bytedeco.dnnl.global.dnnl.*;

/** \endcond
 <p>
 *  Primitive attributes.
 * 
 *  @see \ref dev_guide_attributes */
@Namespace("dnnl") @Properties(inherit = org.bytedeco.dnnl.presets.dnnl.class)
public class primitive_attr extends dnnl_primitive_attr_handle {
    static { Loader.load(); }

    
        public primitive_attr() { super((Pointer)null); allocate(); }
        private native void allocate();
        public primitive_attr(@Const @ByRef primitive_attr arg0) { super((Pointer)null); allocate(arg0); }
        private native void allocate(@Const @ByRef primitive_attr arg0);
        
        ///
        public primitive_attr(dnnl_primitive_attr t, @Cast("bool") boolean weak/*=false*/) { super((Pointer)null); allocate(t, weak); }
        private native void allocate(dnnl_primitive_attr t, @Cast("bool") boolean weak/*=false*/);
        public primitive_attr(dnnl_primitive_attr t) { super((Pointer)null); allocate(t); }
        private native void allocate(dnnl_primitive_attr t);
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public primitive_attr(Pointer p) { super(p); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public primitive_attr(long size) { super((Pointer)null); allocateArray(size); }
    private native void allocateArray(long size);
    @Override public primitive_attr position(long position) {
        return (primitive_attr)super.position(position);
    }
    @Override public primitive_attr getPointer(long i) {
        return new primitive_attr((Pointer)this).position(position + i);
    }


    /** Constructs default (empty) primitive attributes. */

    /** Creates primitive attributes from a C API ::dnnl_primitive_attr_t
     *  handle. The resulting handle is not weak and the C handle will be
     *  destroyed during the destruction of the C++ object.
     * 
     *  @param attr The C API primitive attributes. */
    

    /** Returns the scratchpad mode. */
    
    ///
    public native scratchpad_mode get_scratchpad_mode();

    /** Sets scratchpad mode.
     * 
     *  @param mode Specified scratchpad mode. */
    
    ///
    public native void set_scratchpad_mode(scratchpad_mode mode);
    public native void set_scratchpad_mode(@Cast("dnnl::scratchpad_mode") int mode);

    /** Returns output scaling factors correspondence mask and values.
     * 
     *  @param mask Scaling factors correspondence mask that defines the
     *      correspondence between the output tensor dimensions and the \p
     *      scales vector. The set i-th bit indicates that a dedicated output
     *      scaling factor is used for each index along that dimension. The
     *      mask value of 0 implies a common output scaling factor for the
     *      whole output tensor.
     *  @param scales Vector of output scaling factors. */
    
    ///
    ///
    ///
    ///
    ///
    ///
    public native void get_output_scales(@ByRef IntPointer mask, @StdVector FloatPointer scales);
    public native void get_output_scales(@ByRef IntBuffer mask, @StdVector FloatBuffer scales);
    public native void get_output_scales(@ByRef int[] mask, @StdVector float[] scales);

    /** Sets output scaling factors correspondence mask and values.
     * 
     *  Example usage:
     *  <pre>{@code
     *      int mb = 32, oc = 32,
     *          oh = 14, ow = 14; // convolution output params
     *      // unique output scales per output channel
     *      vector<float> scales = { ... };
     *      int oc_dim = 1; // mb_dim = 0, channel_dim = 1, height_dim = 2, ...
     * 
     *      // construct a convolution descriptor
     *      dnnl::convolution::desc conv_d;
     * 
     *      dnnl::primitive_attr attr;
     *      attr.set_output_scales(attr, oc, 1 << oc_dim, scales);
     * 
     *      dnnl::primitive_desc conv_pd(conv_d, attr, engine);
     *  }</pre>
     * 
     *  \note
     *      The order of dimensions does not depend on how elements are laid
     *      out in memory. For example:
     *      - for a 2D CNN activations tensor the order is always (n, c)
     *      - for a 4D CNN activations tensor the order is always (n, c, h, w)
     *      - for a 5D CNN weights tensor the order is always
     *         (g, oc, ic, kh, kw)
     * 
     *  @param mask Defines the correspondence between the output tensor
     *      dimensions and the \p scales vector. The set i-th bit indicates
     *      that a dedicated scaling factor is used for each index along that
     *      dimension. Set the mask to 0 to use a common output scaling factor
     *      for the whole output tensor.
     *  @param scales Constant vector of output scaling factors. If the
     *      scaling factors are known at the time of this call, the following
     *      equality must hold:
     *      {@code scales.size() = \prod\limits_{d \in mask} output.dims[d].}
     *      Violations can only be detected when the attributes
     *      are used to create a primitive descriptor.
     *      If the scaling factors are not known at the time of the call,
     *      this vector must contain a single #DNNL_RUNTIME_F32_VAL value and
     *      the output scaling factors must be passed at execution time as an
     *      argument with index #DNNL_ARG_ATTR_OUTPUT_SCALES. */
    
    ///
    public native void set_output_scales(int mask, @StdVector FloatPointer scales);
    public native void set_output_scales(int mask, @StdVector FloatBuffer scales);
    public native void set_output_scales(int mask, @StdVector float[] scales);

    /** Returns scaling factors correspondence mask and values for a given
     *  memory argument.
     * 
     *  @param arg Parameter argument index as passed to the
     *      primitive::execute() call.
     *  @param mask Scaling factors correspondence mask that defines the
     *      correspondence between the output tensor dimensions and the \p
     *      scales vector. The set i-th bit indicates that a dedicated scaling
     *      factor is used for each index along that dimension. Set the mask to
     *      0 to use a common scaling factor for the whole output tensor.
     *  @param scales Output vector of scaling factors. */
    
    ///
    ///
    public native void get_scales(int arg, @ByRef IntPointer mask, @StdVector FloatPointer scales);
    public native void get_scales(int arg, @ByRef IntBuffer mask, @StdVector FloatBuffer scales);
    public native void get_scales(int arg, @ByRef int[] mask, @StdVector float[] scales);

    /** Sets scaling factors for primitive operations for a given memory
     *  argument.
     * 
     *  @see dnnl_primitive_attr_set_scales
     *  @see dnnl::primitive_attr::set_output_scales
     * 
     *  @param arg Parameter argument index as passed to the
     *      primitive::execute() call.
     *  @param mask Scaling factors correspondence mask that defines the
     *      correspondence between the tensor dimensions and the \p scales
     *      vector. The set i-th bit indicates that a dedicated scaling factor
     *      is used for each index along that dimension. Set the mask to 0 to
     *      use a common scaling factor for the whole output tensor.
     *  @param scales Constant vector of scaling factors. The following equality
     *      must hold:
     *      {@code scales.size() = \prod\limits_{d \in mask} argument.dims[d].} */
    
    ///
    public native void set_scales(int arg, int mask, @StdVector FloatPointer scales);
    public native void set_scales(int arg, int mask, @StdVector FloatBuffer scales);
    public native void set_scales(int arg, int mask, @StdVector float[] scales);

    /** Returns zero points correspondence mask and values.
     * 
     *  @param arg Parameter argument index as passed to the
     *      primitive::execute() call.
     *  @param mask Zero points correspondence mask that defines the
     *      correspondence between the output tensor dimensions and the \p
     *      zero_points vector. The set i-th bit indicates that a dedicated
     *      zero point is used for each index along that dimension. Set the
     *      mask to 0 to use a common zero point for the whole output tensor.
     *  @param zero_points Output vector of zero points. */
    
    ///
    ///
    public native void get_zero_points(
                int arg, @ByRef IntPointer mask, @StdVector IntPointer zero_points);
    public native void get_zero_points(
                int arg, @ByRef IntBuffer mask, @StdVector IntBuffer zero_points);
    public native void get_zero_points(
                int arg, @ByRef int[] mask, @StdVector int[] zero_points);

    /** Sets zero points for primitive operations for a given memory argument.
     * 
     *  @see dnnl_primitive_attr_set_zero_points
     *  @see dnnl::primitive_attr::set_output_scales
     * 
     *  @param arg Parameter argument index as passed to the
     *      primitive::execute() call.
     *  @param mask Zero point correspondence mask that defines the
     *      correspondence between the tensor dimensions and the \p
     *      zero_points vector. The set i-th bit indicates that a dedicated
     *      zero point is used for each index along that dimension. Set the
     *      mask to 0 to use a common zero point for the whole output tensor.
     *  @param zero_points Constant vector of zero points. If the zero points
     *      are known at the time of this call, the following equality must
     *      hold: {@code zero\_points.size() = \prod\limits_{d \in mask}
     *      argument.dims[d].} If the zero points are not known at the time
     *      of the call, this vector must contain a single
     *      #DNNL_RUNTIME_S32_VAL value and the zero points must be passed at
     *      execution time as an argument with index
     *      #DNNL_ARG_ATTR_ZERO_POINTS. */
    
    ///
    public native void set_zero_points(
                int arg, int mask, @StdVector IntPointer zero_points);
    public native void set_zero_points(
                int arg, int mask, @StdVector IntBuffer zero_points);
    public native void set_zero_points(
                int arg, int mask, @StdVector int[] zero_points);

    /** Returns post-ops previously set via set_post_ops().
     * 
     *  @return Post-ops. */
    
    ///
    ///
    public native @Const @ByVal post_ops get_post_ops();

    /** Sets post-ops.
     * 
     *  \note
     *      There is no way to check whether the post-ops would be supported
     *      by the target primitive. Any error will be reported
     *      by the respective primitive descriptor constructor.
     * 
     *  @param ops Post-ops object to copy post-ops from. */
    
    ///
    ///
    ///
    ///
    ///
    ///
    ///
    ///
    public native void set_post_ops(@Const @ByVal post_ops ops);

    /** Sets quantization scale and shift parameters for RNN data tensors.
     * 
     *  For performance reasons, the low-precision configuration of the RNN
     *  primitives expect input activations to have the unsigned 8-bit integer
     *  data type. The scale and shift parameters are used to quantize
     *  floating-point data to unsigned integer and must be passed to the RNN
     *  primitive using attributes.
     * 
     *  The quantization formula is {@code scale * data + shift}.
     * 
     *  Example usage:
     *  <pre>{@code
     *      // RNN parameters
     *      int l = 2, t = 2, mb = 32, sic = 32, slc = 32, dic = 32, dlc = 32;
     *      // Activations quantization parameters
     *      float scale = 63.f, shift = 64.f;
     * 
     *      primitive_attr attr;
     * 
     *      // Set scale and shift for int8 quantization of activation
     *      attr.set_rnn_data_qparams(scale, shift);
     * 
     *      // Create and configure rnn op_desc
     *      vanilla_rnn_forward::desc rnn_d(/* arguments * /);
     *      vanilla_rnn_forward::primitive_desc rnn_d(rnn_d, attr, engine);
     *  }</pre>
     * 
     *  \note
     *      Quantization scale and shift are common for src_layer, src_iter,
     *      dst_iter, and dst_layer.
     * 
     *  @param scale The value to scale the data by.
     *  @param shift The value to shift the data by. */
    
    ///
    ///
    public native void set_rnn_data_qparams(float scale, float shift);

    /** Returns the quantization scale and shift parameters for RNN data
     *  tensors.
     * 
     *  \note
     *      Quantization scale and shift are common for src_layer, src_iter,
     *      dst_iter, and dst_layer.
     * 
     *  @param scale The value to scale the data by.
     *  @param shift The value to shift the data by. */
    
    ///
    ///
    ///
    public native void get_rnn_data_qparams(@ByRef FloatPointer scale, @ByRef FloatPointer shift);
    public native void get_rnn_data_qparams(@ByRef FloatBuffer scale, @ByRef FloatBuffer shift);
    public native void get_rnn_data_qparams(@ByRef float[] scale, @ByRef float[] shift);

    /** Sets quantization scaling factors for RNN weights tensors. The
     *  low-precision configuration of the RNN primitives expect input weights
     *  to use the signed 8-bit integer data type. The scaling factors are
     *  used to quantize floating-point data to signed integer and must be
     *  passed to RNN primitives using attributes.
     * 
     *  \note
     *      The dimension order is always native and does not depend on the
     *      actual layout used. For example, five-dimensional weights always
     *      have (l, d, i, g, o) logical dimension ordering.
     * 
     *  \note
     *      Quantization scales are common for weights_layer and
     *      weights_iteration
     * 
     *  @param mask Scaling factors correspondence mask that defines the
     *      correspondence between the output tensor dimensions and the \p
     *      scales vector. The set i-th bit indicates that a dedicated scaling
     *      factor should be used each index along that dimension. Set the
     *      mask to 0 to use a common scaling factor for the whole output
     *      tensor.
     *  @param scales Constant vector of output scaling factors. The following
     *      equality must hold:
     *      {@code scales.size() = \prod\limits_{d \in mask} weights.dims[d].}
     *      Violations can only be detected when the attributes are used to
     *      create a primitive descriptor. */
    
    ///
    ///
    public native void set_rnn_weights_qparams(int mask, @StdVector FloatPointer scales);
    public native void set_rnn_weights_qparams(int mask, @StdVector FloatBuffer scales);
    public native void set_rnn_weights_qparams(int mask, @StdVector float[] scales);

    /** Returns the quantization scaling factors for RNN projection weights
     *  tensors.
     * 
     *  \note
     *      The dimension order is always native and does not depend on the
     *      actual layout used. For example, five-dimensional weights always
     *      have (l, d, i, g, o) logical dimension ordering.
     * 
     *  @param mask Scaling factors correspondence mask that defines the
     *      correspondence between the output tensor dimensions and the \p
     *      scales vector. The set i-th bit indicates that a dedicated scaling
     *      factor should be used each index along that dimension. Set the
     *      mask to 0 to use a common scaling factor for the whole output
     *      tensor.
     *  @param scales Constant vector of output scaling factors. The following
     *      equality must hold:
     *      {@code scales.size() = \prod\limits_{d \in mask} weights.dims[d].}
     *      Violations can only be detected when the attributes are used to
     *      create a primitive descriptor. */
    
    ///
    ///
    ///
    public native void get_rnn_weights_qparams(@ByRef IntPointer mask, @StdVector FloatPointer scales);
    public native void get_rnn_weights_qparams(@ByRef IntBuffer mask, @StdVector FloatBuffer scales);
    public native void get_rnn_weights_qparams(@ByRef int[] mask, @StdVector float[] scales);

    /** Sets quantization scaling factors for RNN projection weights tensors. */
    //  The low-precision configuration of the RNN primitives expect input
    //  weights to use the signed 8-bit integer data type. The scaling factors
    //  are used to quantize floating-point data to signed integer and must be
    /** passed to RNN primitives using attributes.
    /**
    /** \note
    /**     The dimension order is always native and does not depend on the
    /**     actual layout used. For example, five-dimensional weights always
    /**     have (l, d, i, g, o) logical dimension ordering.
    /**
    /** \note
    /**     Quantization scales are common for weights_layer and
    /**     weights_iteration
    /**
    /** @param mask Scaling factors correspondence mask that defines the
    /**     correspondence between the output tensor dimensions and the \p
    /**     scales vector. The set i-th bit indicates that a dedicated scaling
    /**     factor should be used each index along that dimension. Set the
    /**     mask to 0 to use a common scaling factor for the whole output
    /**     tensor.
    /** @param scales Constant vector of output scaling factors. The following
    /**     equality must hold:
    /**     {@code scales.size() = \prod\limits_{d \in mask} weights.dims[d].}
    /**     Violations can only be detected when the attributes are used to
    /**     create a primitive descriptor. */
    
    ///
    ///
    public native void set_rnn_weights_projection_qparams(
                int mask, @StdVector FloatPointer scales);
    public native void set_rnn_weights_projection_qparams(
                int mask, @StdVector FloatBuffer scales);
    public native void set_rnn_weights_projection_qparams(
                int mask, @StdVector float[] scales);

    /** Returns the quantization scaling factors for RNN projection weights
     *  tensors.
     * 
     *  \note
     *      The dimension order is always native and does not depend on the
     *      actual layout used. For example, five-dimensional weights always
     *      have (l, d, i, g, o) logical dimension ordering.
     * 
     *  @param mask Scaling factors correspondence mask that defines the
     *      correspondence between the output tensor dimensions and the \p
     *      scales vector. The set i-th bit indicates that a dedicated scaling
     *      factor should be used each index along that dimension. Set the
     *      mask to 0 to use a common scaling factor for the whole output
     *      tensor.
     *  @param scales Constant vector of output scaling factors. The following
     *      equality must hold:
     *      {@code scales.size() = \prod\limits_{d \in mask} weights.dims[d].}
     *      Violations can only be detected when the attributes are used to
     *      create a primitive descriptor. */
    public native void get_rnn_weights_projection_qparams(
                @ByRef IntPointer mask, @StdVector FloatPointer scales);
    public native void get_rnn_weights_projection_qparams(
                @ByRef IntBuffer mask, @StdVector FloatBuffer scales);
    public native void get_rnn_weights_projection_qparams(
                @ByRef int[] mask, @StdVector float[] scales);
}
