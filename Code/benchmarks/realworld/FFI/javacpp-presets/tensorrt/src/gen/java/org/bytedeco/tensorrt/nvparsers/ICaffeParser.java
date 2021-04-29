// Targeted by JavaCPP version 1.5.5-SNAPSHOT: DO NOT EDIT THIS FILE

package org.bytedeco.tensorrt.nvparsers;

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

import static org.bytedeco.tensorrt.global.nvparsers.*;

/**
 *  \class ICaffeParser
 * 
 *  \brief Class used for parsing Caffe models.
 * 
 *  Allows users to export models trained using Caffe to TRT.
 * 
 *  \warning Do not inherit from this class, as doing so will break forward-compatibility of the API and ABI.
 *  */
@Namespace("nvcaffeparser1") @Properties(inherit = org.bytedeco.tensorrt.presets.nvparsers.class)
public class ICaffeParser extends Pointer {
    static { Loader.load(); }
    /** Pointer cast constructor. Invokes {@link Pointer#Pointer(Pointer)}. */
    public ICaffeParser(Pointer p) { super(p); }

    /**
     *  \brief Parse a prototxt file and a binaryproto Caffe model to extract
     *    network definition and weights associated with the network, respectively.
     * 
     *  @param deploy The plain text, prototxt file used to define the network definition.
     *  @param model The binaryproto Caffe model that contains the weights associated with the network.
     *  @param network Network in which the CaffeParser will fill the layers.
     *  @param weightType The type to which the weights will transformed.
     * 
     *  @return A pointer to an IBlobNameToTensor object that contains the extracted data.
     * 
     *  @see nvcaffeparser1::IBlobNameToTensor
     *  */
    
    
    //!
    //!
    //!
    //!
    //!
    public native @Const IBlobNameToTensor parse(String deploy,
                                               String model,
                                               @ByRef INetworkDefinition network,
                                               DataType weightType);
    public native @Const IBlobNameToTensor parse(@Cast("const char*") BytePointer deploy,
                                               @Cast("const char*") BytePointer model,
                                               @ByRef INetworkDefinition network,
                                               @Cast("nvinfer1::DataType") int weightType);

    /**
     *  \brief Parse a deploy prototxt a binaryproto Caffe model from memory buffers to extract
     *    network definition and weights associated with the network, respectively.
     * 
     *  @param deployBuffer The plain text deploy prototxt used to define the network definition.
     *  @param deployLength The length of the deploy buffer.
     *  @param modelBuffer The binaryproto Caffe memory buffer that contains the weights associated with the network.
     *  @param modelLength The length of the model buffer.
     *  @param network Network in which the CaffeParser will fill the layers.
     *  @param weightType The type to which the weights will transformed.
     * 
     *  @return A pointer to an IBlobNameToTensor object that contains the extracted data.
     * 
     *  @see nvcaffeparser1::IBlobNameToTensor
     *  */
    
    
    //!
    //!
    //!
    //!
    //!
    //!
    public native @Const IBlobNameToTensor parseBuffers(String deployBuffer,
                                                      @Cast("std::size_t") long deployLength,
                                                      String modelBuffer,
                                                      @Cast("std::size_t") long modelLength,
                                                      @ByRef INetworkDefinition network,
                                                      DataType weightType);
    public native @Const IBlobNameToTensor parseBuffers(@Cast("const char*") BytePointer deployBuffer,
                                                      @Cast("std::size_t") long deployLength,
                                                      @Cast("const char*") BytePointer modelBuffer,
                                                      @Cast("std::size_t") long modelLength,
                                                      @ByRef INetworkDefinition network,
                                                      @Cast("nvinfer1::DataType") int weightType);

    /**
     *  \brief Parse and extract data stored in binaryproto file.
     * 
     *  The binaryproto file contains data stored in a binary blob. parseBinaryProto() converts it
     *  to an IBinaryProtoBlob object which gives the user access to the data and meta-data about data.
     * 
     *  @param fileName Path to file containing binary proto.
     * 
     *  @return A pointer to an IBinaryProtoBlob object that contains the extracted data.
     * 
     *  @see nvcaffeparser1::IBinaryProtoBlob
     *  */
    
    
    //!
    //!
    //!
    //!
    public native IBinaryProtoBlob parseBinaryProto(String fileName);
    public native IBinaryProtoBlob parseBinaryProto(@Cast("const char*") BytePointer fileName);

    /**
     *  \brief Set buffer size for the parsing and storage of the learned model.
     * 
     *  @param size The size of the buffer specified as the number of bytes.
     * 
     *  \note  Default size is 2^30 bytes.
     *  */
    
    
    //!
    //!
    //!
    public native void setProtobufBufferSize(@Cast("size_t") long size);

    /**
     *  \brief Set the IPluginFactory used to create the user defined plugins.
     * 
     *  @param factory Pointer to an instance of the user implmentation of IPluginFactory.
     *  */
    
    
    //!
    //!
    //!
    public native void setPluginFactory(IPluginFactory factory);

    /**
     *  \brief Set the IPluginFactoryExt used to create the user defined pluginExts.
     * 
     *  @param factory Pointer to an instance of the user implmentation of IPluginFactoryExt.
     *  */
    
    
    //!
    //!
    public native void setPluginFactoryExt(IPluginFactoryExt factory);

    /**
     *  \brief Destroy this ICaffeParser object.
     *  */
    
    
    //!
    //!
    //!
    public native void destroy();

    /**
     *  \brief Set the IPluginFactoryV2 used to create the user defined pluginV2 objects.
     * 
     *  @param factory Pointer to an instance of the user implmentation of IPluginFactoryV2.
     *  */
    
    
    //!
    //!
    public native void setPluginFactoryV2(IPluginFactoryV2 factory);

    /**
     *  \brief Set the namespace used to lookup and create plugins in the network.
     *  */
    public native void setPluginNamespace(String libNamespace);
    public native void setPluginNamespace(@Cast("const char*") BytePointer libNamespace);
    /**
     *  \brief Set the ErrorRecorder for this interface
     * 
     *  Assigns the ErrorRecorder to this interface. The ErrorRecorder will track all errors during execution.
     *  This function will call incRefCount of the registered ErrorRecorder at least once. Setting
     *  recorder to nullptr unregisters the recorder with the interface, resulting in a call to decRefCount if
     *  a recorder has been registered.
     * 
     *  @param recorder The error recorder to register with this interface.
     * 
     *  @see getErrorRecorder
     *  */
    
    
    //!
    //!
    //!
    //!
    //!
    public native void setErrorRecorder(IErrorRecorder recorder);

    /**
     *  \brief get the ErrorRecorder assigned to this interface.
     * 
     *  Retrieves the assigned error recorder object for the given class. A default error recorder does not exist,
     *  so a nullptr will be returned if setErrorRecorder has not been called.
     * 
     *  @return A pointer to the IErrorRecorder object that has been registered.
     * 
     *  @see setErrorRecorder
     *  */
    public native IErrorRecorder getErrorRecorder();
}