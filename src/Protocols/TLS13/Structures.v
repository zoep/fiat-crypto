Require Import Nat Program Omega.

Definition uint8  := { n | n < 2^8 }.
Definition uint16 := { n | n < 2^16 }.
Definition uint24 := { n | n < 2^24 }.
Definition uint32 := { n | n < 2^32 }.

Axiom tuple : Type -> nat -> Type.
Local Infix "^" := tuple.

Definition ProtocolVersion := uint16.
Definition Random := uint8^32.
Definition CipherSuite := uint8^2.
(* Definition Extension := list uint8. *)

Variant HandshakeType :=
| client_hello
| server_hello
| new_session_ticket
| end_of_early_data
| hello_retry_request
| encrypted_extensions
| certificate
| certificate_request
| certificate_verify
| finished
| key_update
| message_hash.

(*
Obligation Tactic := program_simpl; omega.
Program Definition encode (t:HandshakeType) : uint8 :=
match t with
| client_hello => 1
| server_hello => 2
| new_session_ticket => 4
| end_of_early_data => 5
| hello_retry_request => 6
| encrypted_extensions => 8
| certificate => 11
| certificate_request => 13
| certificate_verify => 15
| finished => 20
| key_update => 24
| message_hash => 254
end.
*)

Variant ExtensionType :=
| server_name                                 (* RFC 6066 *)
| max_fragment_length                         (* RFC 6066 *)
| status_request                              (* RFC 6066 *)
| supported_groups                            (* RFC 4492, 7919 *)
| signature_algorithms                        (* RFC 5246 *)
| use_srtp                                    (* RFC 5764 *)
| heartbeat                                   (* RFC 6520 *)
| application_layer_protocol_negotiation      (* RFC 7301 *)
| signed_certificate_timestamp                (* RFC 6962 *)
| client_certificate_type                     (* RFC 7250 *)
| server_certificate_type                     (* RFC 7250 *)
| padding                                     (* RFC 7685 *)
| key_share                                   (* [[TLS13] *)
| pre_shared_key                              (* [[TLS13] *)
| early_data                                  (* [[TLS13] *)
| supported_versions                          (* [[TLS13] *)
| cookie                                      (* [[TLS13] *)
| psk_key_exchange_modes                      (* [[TLS13] *)
| certificate_authorities                     (* [[TLS13] *)
| oid_filters                                 (* [[TLS13] *)
| post_handshake_auth                         (* [[TLS13] *)
.

(*
Module ExtensionType.
Program Definition encode (t:ExtensionType) : uint16 :=
  match t with
| server_name => 0
| max_fragment_length => 1
| status_request => 5
| supported_groups => 10
| signature_algorithms => 13
| use_srtp => 14
| heartbeat => 15
| application_layer_protocol_negotiation => 16
| signed_certificate_timestamp => 18
| client_certificate_type => 19
| server_certificate_type => 20
| padding => 21
| key_share => 40
| pre_shared_key => 41
| early_data => 42
| supported_versions => 43
| cookie => 44
| psk_key_exchange_modes => 45
| certificate_authorities => 47
| oid_filters => 48
| post_handshake_auth => 49
  end.
End ExtensionType.
 *)

Variant NamedGroup :=
  (*
       /* Elliptic Curve Groups (ECDHE) */
       secp256r1(0x0017), secp384r1(0x0018), secp521r1(0x0019),
       x25519(0x001D), x448(0x001E),

       /* Finite Field Groups (DHE) */
       ffdhe2048(0x0100), ffdhe3072(0x0101), ffdhe4096(0x0102),
       ffdhe6144(0x0103), ffdhe8192(0x0104),

       /* Reserved Code Points */
       ffdhe_private_use(0x01FC..0x01FF),
       ecdhe_private_use(0xFE00..0xFEFF),
       (0xFFFF)
  *)
  .

Module KeyShareEntry.
Structure KeyShareEntry :=
  {
    group : NamedGroup;
    key_exchange : list uint8;
  }.
End KeyShareEntry. Notation KeyShareEntry := KeyShareEntry.KeyShareEntry.

Definition KeyShare Handshake_msg_type :=
  match Handshake_msg_type with
    | client_hello => list KeyShareEntry (* client_shares<0..2^16-1> *)
    | hello_retry_request => NamedGroup (* selected_group *)
    | server_hello => KeyShareEntry (* server_share *)
    | _ => False
  end.

Module Extension.
Structure Extension Handshake_msg_type :=
  {
    extension_type : ExtensionType;
    extension_data : match extension_type with
                     | key_share => KeyShare Handshake_msg_type
                     | _ => list uint8 (* TODO *)
                     end
  }.
End Extension. Notation Extension := Extension.Extension.

Module ClientHello.
Structure ClientHello :=
  {
       legacy_version : ProtocolVersion;
       random : Random;
       legacy_session_id : list uint8;
       cipher_suites : list CipherSuite;
       legacy_compression_methods : list uint8;
       extensions : list (Extension client_hello);
  }.
End ClientHello. Notation ClientHello := ClientHello.ClientHello.

Module ServerHello.
Structure ServerHello :=
  {
    version : ProtocolVersion;
    random : Random;
    cipher_suite : CipherSuite;
    extensions : list (Extension server_hello);
   }.
End ServerHello. Notation ServerHello := ServerHello.ServerHello.

Context (
 EndOfEarlyData
 HelloRetryRequest
 EncryptedExtensions
 CertificateRequest
 Certificate
 CertificateVerify
 Finished
 NewSessionTicket
 KeyUpdate
 : Type).

Module Handshake.
Structure Handshake :=
  {
    msg_type : HandshakeType ;
    length : uint24;
    payload : match msg_type with
              | client_hello =>         ClientHello
              | server_hello =>         ServerHello
              | end_of_early_data =>    EndOfEarlyData
              | hello_retry_request =>  HelloRetryRequest
              | encrypted_extensions => EncryptedExtensions
              | certificate_request =>  CertificateRequest
              | certificate =>          Certificate
              | certificate_verify =>   CertificateVerify
              | finished =>             Finished
              | new_session_ticket =>   NewSessionTicket
              | key_update =>           KeyUpdate

              | message_hash => list uint8
              end
  }.
End Handshake. Notation Handshake := Handshake.Handshake.
