// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.opencv.opencv_text;

import org.bytedeco.javacpp.annotation.Index;
import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;
import static org.bytedeco.openblas.global.openblas_nolapack.*;
import static org.bytedeco.openblas.global.openblas.*;
import org.bytedeco.opencv.opencv_core.*;
import static org.bytedeco.opencv.global.opencv_core.*;
import org.bytedeco.opencv.opencv_imgproc.*;
import static org.bytedeco.opencv.global.opencv_imgproc.*;
import org.bytedeco.opencv.opencv_dnn.*;
import static org.bytedeco.opencv.global.opencv_dnn.*;
import static org.bytedeco.opencv.global.opencv_imgcodecs.*;
import org.bytedeco.opencv.opencv_videoio.*;
import static org.bytedeco.opencv.global.opencv_videoio.*;
import org.bytedeco.opencv.opencv_highgui.*;
import static org.bytedeco.opencv.global.opencv_highgui.*;
import org.bytedeco.opencv.opencv_flann.*;
import static org.bytedeco.opencv.global.opencv_flann.*;
import org.bytedeco.opencv.opencv_features2d.*;
import static org.bytedeco.opencv.global.opencv_features2d.*;
import org.bytedeco.opencv.opencv_ml.*;
import static org.bytedeco.opencv.global.opencv_ml.*;

import static org.bytedeco.opencv.global.opencv_text.*;



/* OCR BeamSearch Decoder */

/** \brief OCRBeamSearchDecoder class provides an interface for OCR using Beam Search algorithm.
<p>
\note
   -   (C++) An example on using OCRBeamSearchDecoder recognition combined with scene text detection can
        be found at the demo sample:
        <https://github.com/opencv/opencv_contrib/blob/master/modules/text/samples/word_recognition.cpp>
 */
@Namespace("cv::text") @NoOffset @Properties(inherit = org.bytedeco.opencv.presets.opencv_text.class)
public class OCRBeamSearchDecoder extends BaseOCR {
    static { Loader.load(); }
    /** Default native constructor. */
    public OCRBeamSearchDecoder() { super((Pointer)null); allocate(); }
    /** Native array allocator. Access with {@link Pointer#position(long)}. */
    public OCRBeamSearchDecoder(long size) { super((Pointer)null); allocateArray(size); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public OCRBeamSearchDecoder(Pointer p) { super(p); }
    private native void allocate();
    private native void allocateArray(long size);
    @Override public OCRBeamSearchDecoder position(long position) {
        return (OCRBeamSearchDecoder)super.position(position);
    }
    @Override public OCRBeamSearchDecoder getPointer(long i) {
        return new OCRBeamSearchDecoder(this).position(position + i);
    }


    /** \brief Callback with the character classifier is made a class.
    <p>
    This way it hides the feature extractor and the classifier itself, so developers can write
    their own OCR code.
    <p>
    The default character classifier and feature extractor can be loaded using the utility function
    loadOCRBeamSearchClassifierCNN with all its parameters provided in
    <https://github.com/opencv/opencv_contrib/blob/master/modules/text/samples/OCRBeamSearch_CNN_model_data.xml.gz>.
     */
    public static class ClassifierCallback extends Pointer {
        static { Loader.load(); }
        /** Default native constructor. */
        public ClassifierCallback() { super((Pointer)null); allocate(); }
        /** Native array allocator. Access with {@link Pointer#position(long)}. */
        public ClassifierCallback(long size) { super((Pointer)null); allocateArray(size); }
        /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
        public ClassifierCallback(Pointer p) { super(p); }
        private native void allocate();
        private native void allocateArray(long size);
        @Override public ClassifierCallback position(long position) {
            return (ClassifierCallback)super.position(position);
        }
        @Override public ClassifierCallback getPointer(long i) {
            return new ClassifierCallback(this).position(position + i);
        }
    
        /** \brief The character classifier must return a (ranked list of) class(es) id('s)
        <p>
        @param image Input image CV_8UC1 or CV_8UC3 with a single letter.
        @param recognition_probabilities For each of the N characters found the classifier returns a list with
        class probabilities for each class.
        @param oversegmentation The classifier returns a list of N+1 character locations' x-coordinates,
        including 0 as start-sequence location.
         */
        public native void eval( @ByVal Mat image, @StdVector DoubleVector recognition_probabilities, @ByRef IntVector oversegmentation );
        public native void eval( @ByVal UMat image, @StdVector DoubleVector recognition_probabilities, @ByRef IntVector oversegmentation );
        public native void eval( @ByVal GpuMat image, @StdVector DoubleVector recognition_probabilities, @ByRef IntVector oversegmentation );

        public native int getWindowSize();
        public native int getStepSize();
    }
    /** \brief Recognize text using Beam Search.
    <p>
    Takes image on input and returns recognized text in the output_text parameter. Optionally
    provides also the Rects for individual text elements found (e.g. words), and the list of those
    text elements with their confidence values.
    <p>
    @param image Input binary image CV_8UC1 with a single text line (or word).
    <p>
    @param output_text Output text. Most likely character sequence found by the HMM decoder.
    <p>
    @param component_rects If provided the method will output a list of Rects for the individual
    text elements found (e.g. words).
    <p>
    @param component_texts If provided the method will output a list of text strings for the
    recognition of individual text elements found (e.g. words).
    <p>
    @param component_confidences If provided the method will output a list of confidence values
    for the recognition of individual text elements found (e.g. words).
    <p>
    @param component_level Only OCR_LEVEL_WORD is supported.
     */
    public native @Override void run(@ByRef Mat image, @StdString @ByRef BytePointer output_text, RectVector component_rects/*=NULL*/,
                         StringVector component_texts/*=NULL*/, FloatVector component_confidences/*=NULL*/,
                         int component_level/*=0*/);
    public native void run(@ByRef Mat image, @StdString @ByRef BytePointer output_text);

    public native @Override void run(@ByRef Mat image, @ByRef Mat mask, @StdString @ByRef BytePointer output_text, RectVector component_rects/*=NULL*/,
                         StringVector component_texts/*=NULL*/, FloatVector component_confidences/*=NULL*/,
                         int component_level/*=0*/);
    public native void run(@ByRef Mat image, @ByRef Mat mask, @StdString @ByRef BytePointer output_text);

    // aliases for scripting
    public native @Str BytePointer run(@ByVal Mat image, int min_confidence, int component_level/*=0*/);
    public native @Str BytePointer run(@ByVal Mat image, int min_confidence);
    public native @Str String run(@ByVal UMat image, int min_confidence, int component_level/*=0*/);
    public native @Str String run(@ByVal UMat image, int min_confidence);
    public native @Str BytePointer run(@ByVal GpuMat image, int min_confidence, int component_level/*=0*/);
    public native @Str BytePointer run(@ByVal GpuMat image, int min_confidence);

    public native @Str BytePointer run(@ByVal Mat image, @ByVal Mat mask, int min_confidence, int component_level/*=0*/);
    public native @Str BytePointer run(@ByVal Mat image, @ByVal Mat mask, int min_confidence);
    public native @Str String run(@ByVal UMat image, @ByVal UMat mask, int min_confidence, int component_level/*=0*/);
    public native @Str String run(@ByVal UMat image, @ByVal UMat mask, int min_confidence);
    public native @Str BytePointer run(@ByVal GpuMat image, @ByVal GpuMat mask, int min_confidence, int component_level/*=0*/);
    public native @Str BytePointer run(@ByVal GpuMat image, @ByVal GpuMat mask, int min_confidence);

    /** \brief Creates an instance of the OCRBeamSearchDecoder class. Initializes HMMDecoder.
    <p>
    @param classifier The character classifier with built in feature extractor.
    <p>
    @param vocabulary The language vocabulary (chars when ASCII English text). vocabulary.size()
    must be equal to the number of classes of the classifier.
    <p>
    @param transition_probabilities_table Table with transition probabilities between character
    pairs. cols == rows == vocabulary.size().
    <p>
    @param emission_probabilities_table Table with observation emission probabilities. cols ==
    rows == vocabulary.size().
    <p>
    @param mode HMM Decoding algorithm. Only OCR_DECODER_VITERBI is available for the moment
    (<http://en.wikipedia.org/wiki/Viterbi_algorithm>).
    <p>
    @param beam_size Size of the beam in Beam Search algorithm.
     */
    public static native @Ptr OCRBeamSearchDecoder create(@Ptr ClassifierCallback classifier,
                                         @StdString BytePointer vocabulary,
                                         @ByVal Mat transition_probabilities_table,
                                         @ByVal Mat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
    public static native @Ptr OCRBeamSearchDecoder create(@Ptr ClassifierCallback classifier,
                                         @StdString String vocabulary,
                                         @ByVal Mat transition_probabilities_table,
                                         @ByVal Mat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
    public static native @Ptr OCRBeamSearchDecoder create(@Ptr ClassifierCallback classifier,
                                         @StdString String vocabulary,
                                         @ByVal UMat transition_probabilities_table,
                                         @ByVal UMat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
    public static native @Ptr OCRBeamSearchDecoder create(@Ptr ClassifierCallback classifier,
                                         @StdString BytePointer vocabulary,
                                         @ByVal UMat transition_probabilities_table,
                                         @ByVal UMat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
    public static native @Ptr OCRBeamSearchDecoder create(@Ptr ClassifierCallback classifier,
                                         @StdString BytePointer vocabulary,
                                         @ByVal GpuMat transition_probabilities_table,
                                         @ByVal GpuMat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
    public static native @Ptr OCRBeamSearchDecoder create(@Ptr ClassifierCallback classifier,
                                         @StdString String vocabulary,
                                         @ByVal GpuMat transition_probabilities_table,
                                         @ByVal GpuMat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );

    /** \brief Creates an instance of the OCRBeamSearchDecoder class. Initializes HMMDecoder from the specified path.
    <p>
    \overload
     <p>
     */
    public static native @Ptr OCRBeamSearchDecoder create(@Str BytePointer filename,
                                         @Str BytePointer vocabulary,
                                         @ByVal Mat transition_probabilities_table,
                                         @ByVal Mat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
    public static native @Ptr OCRBeamSearchDecoder create(@Str String filename,
                                         @Str String vocabulary,
                                         @ByVal Mat transition_probabilities_table,
                                         @ByVal Mat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
    public static native @Ptr OCRBeamSearchDecoder create(@Str String filename,
                                         @Str String vocabulary,
                                         @ByVal UMat transition_probabilities_table,
                                         @ByVal UMat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
    public static native @Ptr OCRBeamSearchDecoder create(@Str BytePointer filename,
                                         @Str BytePointer vocabulary,
                                         @ByVal UMat transition_probabilities_table,
                                         @ByVal UMat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
    public static native @Ptr OCRBeamSearchDecoder create(@Str BytePointer filename,
                                         @Str BytePointer vocabulary,
                                         @ByVal GpuMat transition_probabilities_table,
                                         @ByVal GpuMat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
    public static native @Ptr OCRBeamSearchDecoder create(@Str String filename,
                                         @Str String vocabulary,
                                         @ByVal GpuMat transition_probabilities_table,
                                         @ByVal GpuMat emission_probabilities_table,
                                         @Cast("cv::text::decoder_mode") int mode/*=cv::text::OCR_DECODER_VITERBI*/,
                                         int beam_size/*=500*/
        );
}
