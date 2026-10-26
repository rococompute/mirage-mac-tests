let start () =
  Logs.info (fun m ->
      m "using Fortuna, entropy sources: %a"
        Fmt.(list ~sep:(any ", ") Mirage_crypto_rng.Entropy.pp_source)
        (Mirage_crypto_rng.Entropy.sources ()));
  let key = Mirage_crypto_pk.Rsa.generate ~bits:2048 () in
  Logs.info (fun m ->
      m "Generated a RSA key of %d bits" (Mirage_crypto_pk.Rsa.priv_bits key));
  Lwt.return_unit
