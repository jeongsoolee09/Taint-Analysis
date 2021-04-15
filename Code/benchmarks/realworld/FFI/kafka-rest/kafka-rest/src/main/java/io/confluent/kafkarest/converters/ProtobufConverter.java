/*
 * Copyright 2021 Confluent Inc.
 *
 * Licensed under the Confluent Community License (the "License"); you may not use
 * this file except in compliance with the License.  You may obtain a copy of the
 * License at
 *
 * http://www.confluent.io/confluent-community-license
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OF ANY KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations under the License.
 */

package io.confluent.kafkarest.converters;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.google.protobuf.Message;
import io.confluent.kafka.schemaregistry.protobuf.ProtobufSchemaUtils;
import java.io.IOException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Provides conversion of JSON to/from Protobuf.
 */
public final class ProtobufConverter implements SchemaConverter {

  private static final Logger log = LoggerFactory.getLogger(ProtobufConverter.class);

  private static final ObjectMapper JSON_MAPPER = new ObjectMapper();

  /**
   * Converts Protobuf data to their equivalent JsonNode representation.
   *
   * @param value the value to convert
   * @return an object containing the root JsonNode representing the converted object and the size
   *     in bytes of the data when serialized
   */
  @Override
  public JsonNodeAndSize toJson(Object value) {
    try {
      byte[] bytes = ProtobufSchemaUtils.toJson((Message) value);
      if (bytes == null) {
        return new JsonNodeAndSize(null, 0);
      }
      return new JsonNodeAndSize(JSON_MAPPER.readTree(bytes), bytes.length);
    } catch (IOException e) {
      log.error("Jackson failed to deserialize JSON generated by Protobuf's JSON encoder: ", e);
      throw new ConversionException("Failed to convert Protobuf to JSON: " + e.getMessage());
    } catch (RuntimeException e) {
      log.error("Unexpected exception converting Protobuf to JSON: ", e);
      throw new ConversionException("Failed to convert Protobuf to JSON: " + e.getMessage());
    }
  }
}
