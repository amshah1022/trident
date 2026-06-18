import Trident
import Trident.Common.Equiv

open Trident

#eval do
  let contents ← IO.FS.readFile "kernels/vector_add.ttir"
  let filtered := (contents.splitOn "\n")
    |>.map String.trim
    |>.filter (fun l =>
        !l.isEmpty && !l.startsWith "module" && !l.startsWith "}" &&
        !l.startsWith "tt.func" && !l.startsWith "tt.return" &&
        !l.startsWith "#" && !l.startsWith "//" &&
        !l.startsWith "attributes" &&
        !l.contains "tt.divisibility" &&
        !(l.startsWith "%" && !l.contains " = "))
    |> String.intercalate "\n"
  match parseKernelVerbose filtered with
  | .error e => IO.println s!"Parse error: {e}"
  | .ok kernel => do
      IO.println s!"Parsed {kernel.length} instructions"
      let bs := 4
      let a : List Int := [1, 2, 3, 4]
      let b : List Int := [10, 20, 30, 40]
      let ref := runRef a b 0 bs 1
      let got := runAndExtract kernel a b 0 bs 1
      IO.println s!"ref (bs=4): {ref}"
      IO.println s!"got (bs=4): {got}"
      let bs2 := 1024
      let a2 := (List.range bs2).map (fun i => Int.ofNat (i + 1))
      let b2 := (List.range bs2).map (fun i => Int.ofNat (i * 2))
      let ref2 := runRef a2 b2 0 bs2 1
      let got2 := runAndExtract kernel a2 b2 0 bs2 1
      IO.println s!"ref first 5 (bs=1024): {ref2.take 5}"
      IO.println s!"got first 5 (bs=1024): {got2.take 5}"
