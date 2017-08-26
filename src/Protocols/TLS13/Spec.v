(* from https://raw.githubusercontent.com/tlswg/tls13-spec/master/draft-ietf-tls-tls13.md *)

(**

# Handshake Protocol

The handshake protocol is used to negotiate the security parameters
of a connection. Handshake messages are supplied to the TLS record layer, where
they are encapsulated within one or more TLSPlaintext or TLSCiphertext structures, which are
processed and transmitted as specified by the current active connection state.

%%% Handshake Protocol

       enum {
           hello_request_RESERVED(0),
           client_hello(1),
           server_hello(2),
           hello_verify_request_RESERVED(3),
           new_session_ticket(4),
           end_of_early_data(5),
           hello_retry_request(6),
           encrypted_extensions(8),
           certificate(11),
           server_key_exchange_RESERVED(12),
           certificate_request(13),
           server_hello_done_RESERVED(14),
           certificate_verify(15),
           client_key_exchange_RESERVED(16),
           finished(20),
           key_update(24),
           message_hash(254),
           (255)
       } HandshakeType;

       struct {
           HandshakeType msg_type;    /* handshake type */
           uint24 length;             /* bytes in message */
           select (Handshake.msg_type) {
               case client_hello:          ClientHello;
               case server_hello:          ServerHello;
               case end_of_early_data:     EndOfEarlyData;
               case hello_retry_request:   HelloRetryRequest;
               case encrypted_extensions:  EncryptedExtensions;
               case certificate_request:   CertificateRequest;
               case certificate:           Certificate;
               case certificate_verify:    CertificateVerify;
               case finished:              Finished;
               case new_session_ticket:    NewSessionTicket;
               case key_update:            KeyUpdate;
           };
       } Handshake;

Protocol messages MUST be sent in the order defined in
{{the-transcript-hash}} and shown in the diagrams in {{protocol-overview}}.
A peer which receives a handshake message in an unexpected order
MUST abort the handshake with an "unexpected_message" alert.
 *)

(* HOW TO ENCODE: Have a function [list of trace-seen-so-far -> list
(sender * HandshakeType)]; encode the list of messages from
{{the-transcript-hash}}; require that one list be a sublist of the
other one. *)

(**

New handshake message types are assigned by IANA as described in
{{iana-considerations}}.


## Key Exchange Messages

The key exchange messages are used to determine the security capabilities
of the client and the server and to establish shared secrets including
the traffic keys used to protect the rest of the handshake and the data.

### Cryptographic Negotiation

In TLS, the cryptographic negotiation proceeds by the client offering the
following four sets of options in its ClientHello:

 *)

(* Constraint: Session starts with ClientHello *)

(**

- A list of cipher suites which indicates the AEAD algorithm/HKDF hash
  pairs which the client supports.

 *)

(* Client Constraint: Per-Connection decision of list of which suites are
supported; list in ClientHello must be Leibniz equal to the list of
supported suites. *)

(**
- A "supported_groups" ({{negotiated-groups}}) extension which indicates the (EC)DHE groups
  which the client supports and a "key_share" ({{key-share}}) extension which contains
  (EC)DHE shares for some or all of these groups.
 *)
(* Client Constraint: Per-Connection decision of list of which
groups/key_share are supported; list in ClientHello must be Leibniz
equal to the list of supported groups/key_share. *)
(* Note: key_share is optional/situation-dependent *)
(* TODO: report issue with wording here *)

(**
- A "signature_algorithms" ({{signature-algorithms}}) extension which indicates the signature
  algorithms which the client can accept.
 *)

(* Client Constraint: Per-Connection decision of list of which
signature_algorithms are supported; list in ClientHello must be
Leibniz equal to the list chosen. *)

(**
- A "pre_shared_key" ({{pre-shared-key-extension}}) extension which
  contains a list of symmetric key identities known to the client and a
  "psk_key_exchange_modes" ({{pre-shared-key-exchange-modes}})
  extension which indicates the key exchange modes that may be used
  with PSKs.
 *)

(* Client constraint: long-lived (across connections) global state of
which key identities are known.  Note: optional *)
(* How to implement: Global (cross-connection) list of "additions to
pre_shared_key" up to this point (up to the current message); when
filtering multi-connection traces for a particular connection, also
filter the list of additions.  Pass in this list of additions, as well
as the initial list (which may or may not be empty), at the
ClientHello, if you send pre_shared_key, the set you send must be a
subset (sublist up to permutation) of the initial list + the list of
additions at the point of the client hello. *)

(**
If the server does not select a PSK, then the first three of these
options are entirely orthogonal: the server independently selects a
cipher suite, an (EC)DHE group and key share for key establishment,
and a signature algorithm/certificate pair to authenticate itself to
the client. If there is no overlap between the received "supported_groups"
and the groups supported by the server then the server MUST abort the
handshake with a "handshake_failure" or an "insufficient_security" alert.

 *)

(* Note: these constraints don't mandate a ServerHello; they mandate
that any ServerHello you do send agrees with these decisions. *)

(* Server constraint: per-connection decision: pick option PSK; pick
option (suite+group+key share+sig algorithm/cert pair) *)
(* Server constraint: if you pick group / key_share, the group &
key share MUST be in the lists given by the client. *)
(* Server constraint: if you pick PSK, then it must be in the client's
list *)
(* Server constraint: if PSK is None and other stuff is None, then you
MUST abort with handshake_failure or with insufficient_security. *)
(* Note: The server is not actually required to make the choice
independently, is it? *)

(**

If the server selects a PSK, then it MUST also select a key
establishment mode from the set indicated by client's
"psk_key_exchange_modes" extension (at present, PSK alone or with (EC)DHE). Note
that if the PSK can be used without (EC)DHE then non-overlap in the
"supported_groups" parameters need not be fatal, as it is in the
non-PSK case discussed in the previous paragraph.

 *)

(* Server constraint: per-connection choice of option PSK-mode; if PSK
is not none and client presented a psk_key_exchange_modes list, then
the server MUST send a PSK mode that's in the list *)

(**

If the server selects an (EC)DHE group and the client did not offer a
compatible "key_share" extension in the initial ClientHello, the server MUST
respond with a HelloRetryRequest ({{hello-retry-request}}) message.

 *)

(* Server constraint: per-connection choice of option group; if the
group has no compatible key_share, next message must be
HelloRetryRequest with the selected group *)

(**

If the server successfully selects parameters and does not require a
HelloRetryRequest, it indicates the selected parameters in the ServerHello as
follows:

 *)

(* TODO: Request clarification: can the server send a
HelloRetryRequest with a group for which the client did, in fact,
offer a compatible "key_share" extension?  Or is it required to send a
ServerHello if it can, for the selected group? *)

(**

- If PSK is being used, then the server will send a
  "pre_shared_key" extension indicating the selected key.

 *)

(* Server constraint: ^ *)

(**

- If PSK is not being used, then (EC)DHE and certificate-based
  authentication are always used.

 *)

(* Server constraint: ^ *)

(**

- When (EC)DHE is in use, the server will also provide a
  "key_share" extension.

 *)

(* Server constraint: ^ *)

(**

- When authenticating via a certificate, the server will send
  the Certificate ({{certificate}}) and CertificateVerify
  ({{certificate-verify}}) messages. In TLS 1.3
  as defined by this document, either a PSK or a certificate
  is always used, but not both. Future documents may define how
  to use them together.

 *)

(* Server constraint: If PSK is None (c.f. bullet point 2), then, if
server Finished appears in the transcript, Certificate and
CertificateVerify must be sent by the server before that *)

(**

If the server is unable to negotiate a supported set of parameters
(i.e., there is no overlap between the client and server parameters),
it MUST abort the handshake with either
a "handshake_failure" or "insufficient_security" fatal alert
(see {{alert-protocol}}).

 *)

(* Server constraint: If you send anything other than ServerHello or
HelloRetryRequest, then it must be an abort with handshake_failure or
insufficient_security *)

(**

###  Client Hello

When a client first connects to a server, it is REQUIRED to send the
ClientHello as its first message. The client will also send a
ClientHello when the server has responded to its ClientHello with a
HelloRetryRequest. In that case, the client MUST send the same
ClientHello (without modification) except:

 *)

(* Duplicate Client Constraint: Session starts with ClientHello *)
(* Client Constraint: If you get HelloRetryRequest, MUST respond with
ClientHello if you respond at all *)

(**
- If a "key_share" extension was supplied in the HelloRetryRequest,
  replacing the list of shares with a list containing a single
  KeyShareEntry from the indicated group.

 *)

(* Client Constraint: ^ *)

(**
- Removing the "early_data" extension ({{early-data-indication}}) if one was
  present. Early data is not permitted after HelloRetryRequest.

 *)

(* Client Constraint: ^ *)

(**
- Including a "cookie" extension if one was provided in the
  HelloRetryRequest.

 *)

(* Client Constraint: ^ (Note: Required) *)

(**
- Updating the "pre_shared_key" extension if present by
  recomputing the "obfuscated_ticket_age" and binder values
  and (optionally) removing
  any PSKs which are incompatible with the server's indicated
  cipher suite.
 *)

(* Client Constraint: Computed pre_shared_key must be re-computed with
new randomness and with the same inputs as before, modulo possibly
removing incompatible keys. *)

(**

Because TLS 1.3 forbids renegotiation, if a server has negotiated TLS
1.3 and receives a ClientHello at any other time, it MUST terminate
the connection with an "unexpected_message" alert.

 *)

(* Server constraint: If there's a ClientHello after anything other
than connection start or HelloRetryRequest, abort with
unexpected_message.  Note that aborting (but not the alert?) is
mandated by transcript hash. *)

(**

If a server established a TLS connection with a previous version of TLS
and receives a TLS 1.3 ClientHello in a renegotiation, it MUST retain the
previous protocol version. In particular, it MUST NOT negotiate TLS 1.3.

 *)

(* Note: We're not implementing any older protocols *)

(**

Structure of this message:

%%% Key Exchange Messages

       uint16 ProtocolVersion;
       opaque Random[32];

       uint8 CipherSuite[2];    /* Cryptographic suite selector */

       struct {
           ProtocolVersion legacy_version = 0x0303;    /* TLS v1.2 */
           Random random;
           opaque legacy_session_id<0..32>;
           CipherSuite cipher_suites<2..2^16-2>;
           opaque legacy_compression_methods<1..2^8-1>;
           Extension extensions<8..2^16-1>;
       } ClientHello;

legacy_version
: In previous versions of TLS, this field was used for version negotiation
  and represented the highest version number supported by the client.
  Experience has shown that many servers do not properly implement
  version negotiation, leading to "version intolerance" in which
  the server rejects an otherwise acceptable ClientHello with a version
  number higher than it supports.
  In TLS 1.3, the client indicates its version preferences in the
  "supported_versions" extension ({{supported-versions}}) and the legacy_version field MUST
  be set to 0x0303, which is the version number for TLS 1.2.
  (See {{backward-compatibility}} for details about backward compatibility.)

random
: 32 bytes generated by a secure random number generator.
  See {{implementation-notes}} for additional information.

legacy_session_id
: Versions of TLS before TLS 1.3 supported a "session resumption"
  feature which has been merged with Pre-Shared Keys in this version
  (see {{resumption-and-psk}}).
  This field MUST be ignored by a server negotiating TLS 1.3 and
  MUST be set as a zero length vector (i.e., a single zero byte
  length field) by clients that do not have a cached session ID
  set by a pre-TLS 1.3 server.

 *)

(* Note: We're not implementing any older protocols *)

(**

cipher_suites
: This is a list of the symmetric cipher options supported by the
  client, specifically the record protection algorithm (including
  secret key length) and a hash to be used with HKDF, in descending
  order of client preference. If the list contains cipher suites that
  the server does not recognize, support or wish to use, the server
  MUST ignore those cipher suites and process the remaining ones as
  usual. Values are defined in {{cipher-suites}}. If the client is
  attempting a PSK key establishment, it SHOULD advertise at least one
  cipher suite indicating a Hash associated with the PSK.

 *)

(* Note: Ignoring unrecognized cipher suites should get spec'd at the
same location as, e.g., spec'ing that the server isn't allowed to
decide to end connections early based on secret data *)

(**

legacy_compression_methods
: Versions of TLS before 1.3 supported compression with the list of
  supported compression methods being sent in this field. For every TLS 1.3
  ClientHello, this vector MUST contain exactly one byte set to
  zero, which corresponds to the "null" compression method in
  prior versions of TLS. If a TLS 1.3 ClientHello is
  received with any other value in this field, the server MUST
  abort the handshake with an "illegal_parameter" alert. Note that TLS 1.3
  servers might receive TLS 1.2 or prior ClientHellos which contain
  other compression methods and MUST follow the procedures for
  the appropriate prior version of TLS.  TLS 1.3 ClientHellos are identified
  as having a legacy_version of 0x0303 and a supported_versions extension
  present with 0x0304 as the highest version indicated therein.

 *)

(* Server constraint: If we recieve ClientHello with anything other
than single zero byte in legacy_compression_methods, we MUST abort
with illegal_parameter. *)

(**

extensions
: Clients request extended functionality from servers by sending
  data in the extensions field.  The actual "Extension" format is
  defined in {{extensions}}.  In TLS 1.3, use
  of certain extensions is mandatory, as functionality is moved into
  extensions to preserve ClientHello compatibility with previous versions of TLS.
  Servers MUST ignore unrecognized extensions.
 *)

(* Note: Ignoring unrecognized extensions should get spec'd at the
same location as, e.g., spec'ing that the server isn't allowed to
decide to end connections early based on secret data *)

(**

{:br }

All versions of TLS allow an extensions field to optionally follow the
compression_methods field. TLS 1.3 ClientHello
messages always contain extensions (minimally "supported_versions", otherwise
they will be interpreted as TLS 1.2 ClientHello messages).
However, TLS 1.3 servers might receive ClientHello messages without an
extensions field from prior versions of TLS.
The presence of extensions can be detected by determining whether there
are bytes following the compression_methods field at the end of the
ClientHello. Note that this method of detecting optional data differs
from the normal TLS method of having a variable-length field, but it
is used for compatibility with TLS before extensions were defined.
TLS 1.3 servers will need to perform this check first and only
attempt to negotiate TLS 1.3 if a "supported_version" extension
is present.
 *)

(* Note: We should be able to encode missing list of extensions as nil
(otherwise as [None : option list]); this happens when decoding
records / wire data. *)

(**
If negotiating a version of TLS prior to 1.3, a server MUST check that
the message either contains no data after legacy_compression_methods
or that it contains a valid extensions block with no data following.
If not, then it MUST abort the handshake with a "decode_error" alert.

In the event that a client requests additional functionality using
extensions, and this functionality is not supplied by the server, the
client MAY abort the handshake.

After sending the ClientHello message, the client waits for a ServerHello
or HelloRetryRequest message. If early data
is in use, the client may transmit early application data
({{zero-rtt-data}}) while waiting for the next handshake message.

 *)

(* TODO: Deal with early data *)

(**
### Server Hello {#server-hello}

The server will send this message in response to a ClientHello message
to proceed with the handshake if it is able to negotiate an acceptable
set of handshake parameters based on the ClientHello.

Structure of this message:

%%% Key Exchange Messages

       struct {
           ProtocolVersion version;
           Random random;
           CipherSuite cipher_suite;
           Extension extensions<6..2^16-1>;
       } ServerHello;

version
: This field contains the version of TLS negotiated for this connection.  Servers
  MUST select a version from the list in ClientHello's supported_versions extension,
  or otherwise negotiate TLS 1.2 or a previous version.
  A client that receives a version that was not offered MUST abort the handshake.
  For this version of the specification, the version is 0x0304.  (See
  {{backward-compatibility}} for details about backward compatibility.)

random
: 32 bytes generated by a secure random number generator.
  See {{implementation-notes}} for additional information.
  The last eight bytes MUST be overwritten as described
  below if negotiating TLS 1.2 or TLS 1.1, but the
  remaining bytes MUST be random.
  This structure is generated by the server and MUST be
  generated independently of the ClientHello.random.

cipher_suite
: The single cipher suite selected by the server from the list in
  ClientHello.cipher_suites. A client which receives a cipher suite
  that was not offered MUST abort the handshake with an "illegal_parameter"
  alert.

extensions
: A list of extensions.  The ServerHello MUST only include extensions
  which are required to establish the cryptographic context. Currently
  the only such extensions are "key_share" and "pre_shared_key".
  All current TLS 1.3 ServerHello messages will contain one of these
  two extensions, or both when using a PSK with (EC)DHE key establishment.
  The remaining extensions are sent separately in the EncryptedExtensions
  message.
{:br }

TLS 1.3 has a downgrade protection mechanism embedded in the server's
random value. TLS 1.3 servers which negotiate TLS 1.2 or below in
response to a ClientHello MUST set the last eight bytes of their
Random value specially.

If negotiating TLS 1.2, TLS 1.3 servers MUST set the last eight bytes of their
Random value to the bytes:

      44 4F 57 4E 47 52 44 01

If negotiating TLS 1.1 or below, TLS 1.3 servers MUST and TLS 1.2
servers SHOULD set the last eight bytes of their Random value to the
bytes:

      44 4F 57 4E 47 52 44 00


TLS 1.3 clients receiving a ServerHello indicating TLS 1.2 or below
MUST check that the last eight bytes are not equal to either of these values.
TLS 1.2 clients SHOULD also check that the last eight bytes are not
equal to the second value if the ServerHello indicates TLS 1.1 or
below.  If a match is found, the client MUST abort the handshake
with an "illegal_parameter" alert.  This mechanism provides limited
protection against downgrade attacks over and above what is provided
by the Finished exchange: because the ServerKeyExchange, a message
present in TLS 1.2 and below, includes a signature over both random
values, it is not possible for an active attacker to modify the
random values without detection as long as ephemeral ciphers are used.
It does not provide downgrade protection when static RSA is used.

Note: This is a change from {{RFC5246}}, so in practice many TLS 1.2 clients
and servers will not behave as specified above.

A legacy TLS client performing renegotiation with TLS 1.2 or prior
and which receives a TLS 1.3 ServerHello during renegotiation
MUST abort the handshake with a "protocol_version" alert.
Note that renegotiation is not possible when TLS 1.3 has been
negotiated.

RFC EDITOR: PLEASE REMOVE THE FOLLOWING PARAGRAPH
Implementations of draft versions (see {{draft-version-indicator}}) of this
specification SHOULD NOT implement this mechanism on either client and server.
A pre-RFC client connecting to RFC servers, or vice versa, will appear to
downgrade to TLS 1.2. With the mechanism enabled, this will cause an
interoperability failure.


###  Hello Retry Request

The server will send this message in response to a ClientHello message if it is
able to find an acceptable set of parameters but the ClientHello does not
contain sufficient information to proceed with the handshake.

Structure of this message:

%%% Key Exchange Messages

       struct {
           ProtocolVersion server_version;
           CipherSuite cipher_suite;
           Extension extensions<2..2^16-1>;
       } HelloRetryRequest;

{:br }

The version, cipher_suite, and extensions fields have the
same meanings as their corresponding values in the ServerHello.
The server SHOULD send only the extensions necessary for the client to
generate a correct ClientHello pair. As with ServerHello, a
HelloRetryRequest MUST NOT contain any extensions that were not first
offered by the client in its ClientHello, with the exception of optionally the
"cookie" (see {{cookie}}) extension.

Upon receipt of a HelloRetryRequest, the client MUST verify that the
extensions block is not empty and otherwise MUST abort the handshake
with a "decode_error" alert. Clients MUST abort the handshake with
an "illegal_parameter" alert if the HelloRetryRequest would not result in
any change in the ClientHello. If a client receives a second
HelloRetryRequest in the same connection (i.e., where
the ClientHello was itself in response to a HelloRetryRequest), it
MUST abort the handshake with an "unexpected_message" alert.

Otherwise, the client MUST process all extensions in the HelloRetryRequest and
send a second updated ClientHello. The HelloRetryRequest extensions defined in
this specification are:

- cookie (see {{cookie}})

- key_share (see {{key-share}})

In addition, in its updated ClientHello, the client SHOULD NOT offer
any pre-shared keys associated with a hash other than that of the
selected cipher suite. This allows the client to avoid having to
compute partial hash transcripts for multiple hashes in the second
ClientHello.  A client which receives a cipher suite that was not
offered MUST abort the handshake.  Servers MUST ensure that they
negotiate the same cipher suite when receiving a conformant updated
ClientHello (if the server selects the cipher suite as the first step
in the negotiation, then this will happen automatically). Upon
receiving the ServerHello, clients MUST check that the cipher suite
supplied in the ServerHello is the same as that in the
HelloRetryRequest and otherwise abort the handshake with an
"illegal_parameter" alert.

*)
