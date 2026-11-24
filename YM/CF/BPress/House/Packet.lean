import YM.CF.BPress.House.Shelves
import YM.CF.BPress.House.Labels
import YM.CF.BPress.Vesper.Sail
import YM.CF.BPress.Port.Honor
/-!
Single state at body.Housing. Θ-spin. We take an extra *normalized* dummy block-version of
 the polytoys (only those whose locations are actually assigned read in U etc.). Contour core
 activities use precisely the probabilities here column-by-column. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.House
open RG Wilson Push.SectorMeasure MeasureTheory LocalH Lattice Cube Bands Locale Wealth Net Grid Finset Function SU Mag Branch Port Weave Vesper Skye Hazel Reserve
open scoped Classical Topology BigOperators YM.CF.BPress.Vesper
variable {N:Side}{B:BandWidth}(A:Bands (More N) B)(R:Hangar (More N)) (y:ℝ)
-- rank dimension.A.Real.W.BankMap
abbrev Platter := Patio R → Pack B.D -- placeholder implicit B need tune signatures
abbrev Encore := Patio R→ Market B.D
abbrev SummerM := Platter (B:=B) R × Encore (B:=B) R
abbrev Hat (N:Side) := Micro (More N) × (Ids N× (Rod N × ActY N))
abbrev Attire := SummerM (B:=B) R × Hat N
abbrev Realm (B:BandWidth)(N:Side)(R:Hangar (More N)) := Bank R× Attire (B:=B) R
abbrev Choir := BlockY A R→ Realm B N R
variable (p : Choir A R)
abbrev icon (i:BlockY A R):= (p i).1
abbrev picnic (i:BlockY A R):= (p i).2.1
abbrev Cc (i:BlockY A R):= (p i).2.2
abbrev scene : Hat N:= (fun i=> (Cc A R p (plan A R i.1)).1 i, fun i=>(Cc A R p (plan A R i)).2.1 i, fun i=>(Cc A R p (plan A R i)).2.2.1 i, fun i=>(Cc A R p (plan A R (node i))).2.2.2 i)
def βread : Fills A:= gather A R (fun i=> (picnic A R p i).1)
def κread : Offers A:= gather A R (fun i=>(picnic A R p i).2)
abbrev keyO : Old A:= beset A R (icon A R p)
abbrev Sread := (keyO A R p).1
abbrev coinT: A.Hcols→ Fin 5 := (keyO A R p).2
abbrev codeT : A.Slates:= flash A (coinT A R p)
abbrev stork : Quarters A:= (βread A R p,κread A R p)
abbrev mState (N:Side){B:BandWidth}(A:Bands (More N) B):= Old A×(Quarters A × Hat N)
def read : mState N A:= (keyO A R p,(stork A R p,scene A R p))
-- probability laws
abbrev gau : Measure (Platter (B:=B) R):=Law.chain (volts B.D y) (Patio R)
abbrev hard : Measure (Encore (B:=B) R):=Law.chain (Rainy B.D) (Patio R)
abbrev summerV : Measure (SummerM (B:=B) R):= (gau (B:=B) R y).prod (hard (B:=B) R)
def paleB (y:ℝ)(N:Side) : Measure (Hat N):=(Law.chain (Law.noise group (xi y)) (Link (More N))).prod ((Skye.depot N).prod ((Wheel.coin (Site (More N))).prod (Wheel.coin (Site N))))
instance : IsFiniteMeasure (paleB y N):=by unfold paleB; infer_instance
def sunny : Measure (Attire (B:=B) R):=(summerV (B:=B) R y).prod (paleB y N)
instance : IsFiniteMeasure (sunny (B:=B) R y):=by unfold sunny; infer_instance
abbrev Training (R:Hangar (More N))(B:BandWidth) (y:ℝ) : Measure (Realm B N R):= (count (Bank R)).prod (sunny (B:=B) R y)
def trainer : Measure (Choir A R):= Law.chain (Training R B y) (BlockY A R)
instance : IsFiniteMeasure (trainer A R y):=by unfold trainer; infer_instance
def museum : Measure (mState N A):= (count _).prod ((knell A y).prod (paleB y N))
instance : IsFiniteMeasure (museum A y):=by unfold museum; infer_instance
-- Π recognition.
variable {y}
structure Fast(y:ℝ):Prop where
 a: 0< xi y
 hb: xi y≤1
variable (z:Fast y)
include z
lemma Fast.noise : IsProbabilityMeasure (Law.noise group (xi y)):= Law.noise_p z.a z.hb
lemma paleQ (N:Side): IsProbabilityMeasure (paleB y N):=by haveI:= z.noise; unfold paleB; infer_instance
lemma summerP : IsProbabilityMeasure (sunny (B:=B) R y):=by haveI:= paleQ z N; unfold sunny; infer_instance -- tune ν
lemma recipe : MeasurePreserving (read A R) (trainer A R y) (museum A y):=by
 haveI:= z.noise; have he : MeasurePreserving (beset A R) (Law.chain (count (Bank R)) (BlockY A R)) (count (Old A)):= by rw [←count_pi]; exact counting (bankUp A R) -- tune
 let I:= BlockY A R; let P:= Patio R; have ht:= reP (volts B.D y) (lodge A R); have hr:=reP (Rainy B.D) (lodge A R); have hs:= splitP I (gau (B:=B) R y) (hard (B:=B) R); let M:= knell A y; let W:=paleB y N; let L:= summerV (B:=B) R y; let K:= M.prod W; have hd:MeasurePreserving (fun x : I→ Hat N => (fun i:Link (More N)=> (x (plan A R i.1)).1 i, fun i:Seat N=>(x (plan A R i)).2.1 i, fun i:Site (More N)=>(x (plan A R i)).2.2.1 i, fun i:Site N=>(x (plan A R (node i))).2.2.2 i): (I→Hat N) → Hat N) (Law.chain W I) W:=by -- syntax type ascription ; Seat
    let A':=Wheel.coin (Site (More N)); let B':=Wheel.coin (Site N); let U:=guest Wheel.circleLaw (plan A R); let V:= guest Wheel.circleLaw (plan A R ∘ node); let f:=(U.prod V).comp (splitP I A' B'); let g:= ( (guest (parcel N) (plan A R)).prod f ).comp (splitP I (Skye.depot N) (A'.prod B')); exact (((guest (Law.noise SU.group (xi y)) (fun i:Link (More N)=> plan A R i.1))).prod g).comp (splitP I (Law.chain (Law.noise group (xi y)) (Link (More N))) ((Skye.depot N).prod (A'.prod B')))
 have hb:MeasurePreserving (fun p:I→Attire (B:=B) R=> (((gather A R (fun i=> (p i).1.1)), gather A R (fun i=> (p i).1.2)),scene A R (fun i=>(Classical.arbitrary _,p i)))) (Law.chain (sunny (B:=B) R y) I) K:= (((ht.prod hr).comp hs).prod hd).comp (splitP I L W)
 exact (he.prod hb).comp (splitP I (count (Bank R)) (sunny (B:=B) R y))
end YM.CF.BPress.House
