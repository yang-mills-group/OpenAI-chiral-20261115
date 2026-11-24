import YM.CF.BProof.Trek.Shaw
/-! Shallow amendments and matching. Designed for both accepted arguments (Mark deep
fields themselves) and homogeneous z reference, not confusing domains. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c:Side}(Y:Yard s)
structure Script where
 X:Y.Index → Site s→ Ballot
 K:Y.Index → Site s→ ℝ → Stamp
 frame : Y.Index→ Site s→ E -- rotation in use (h^-1!) after axial move
 label : Y.Index → Space s→ Fin 5 -- gap orientation
variable {Y}(D:Script Y) {u v d:ℝ}{H: Herald u v}{t:ℕ}(C:Sized t H.whole)
namespace Script
abbrev code(x:Site s):Fin 5:= D.label (tag Y x) (BProof.space x)
def over (x:Site s): Ballot:= let i:=tag Y x; if dark Y x then D.X (hr Y x) x else XG (D.code x) (dial Y i x)
def ramp (C:Sized t H.whole)(i:Y.Index)(x:Site s):= Rise.easeD t C.stepQ (chip (Y.u i) Y.long x)
def stand (C:Sized t H.whole)(i:Y.Index)(x:Site s) : Prop:= chip (Y.u i) Y.long x≤ C.extent
def curv (i:Y.Index)(x: Site s):ℝ→Stamp:= if ¬Y.D i ∧ stand C i x then rosy (D.code x) (D.frame i x) (ramp C i x) else D.K i x
def port (x:Site s) : ℝ→Stamp:= let i:=tag Y x; if dark Y x then curv D C (hr Y x) x else TG (D.code x) (dial Y i x)
lemma over_band (i:Y.Index)(x:Site s)(h:x∈Y.band i): over D x=D.X i x:=by unfold over; dsimp only; rw [if_pos (codeB Y h).1,(codeB Y h).2]
lemma port_band(i:Y.Index)(x:Site s)(h:x∈Y.band i): port D C x=curv D C i x:=by unfold port; dsimp only; rw [if_pos (codeB Y h).1,(codeB Y h).2]
lemma curvD (i:Y.Index)(h:Y.D i)(x:Site s): curv D C i x=D.K i x:= if_neg fun z=>z.1 h
lemma curvSet(i:Y.Index)(h:¬Y.D i)(x:Site s)(p:stand C i x):curv D C i x= rosy (D.code x) (D.frame i x) (ramp C i x):= if_pos ⟨h,p⟩
lemma stand_mem {i:Y.Index}{x:Site s}(p:stand C i x): chip (Y.u i) Y.long x≤t+C.stepQ:=p
end Script
variable (U:Bkg s)(g:Ratio c s)(B:Blocks Y c)
-- name permissions. ground near r chosen R big. distinguish frame closeness and indices exact. speeds on raw band.
structure Permit (D:Script Y)(C:Sized t H.whole)(U:Bkg s)(g:Ratio c s)(B:Blocks Y c)(d:ℝ) : Prop where
 money(i:Y.Index)(x:Site s) (p:x∈ Y.band i) : Money (D.K i x)
 begin(i x)(p:x∈ Y.band i): D.K i x 0= Pair.fullM (D.X i x).val
 Xpay(i): PaceX ↑(Y.band i) U (D.X i) H.good
 Hpay(i)(t)(p:t∈TimeR): SkinH ↑(Y.band i) U (fun x=> D.K i x t) v
 fieldD(i)(h:Y.D i)(x)(p:x∈Y.band i): D.X i x=apex ∧ D.K i x=BM 1
 fieldN(i)(h:¬Y.D i)(x)(p:x∈Y.band i)(u:chip (Y.u i) Y.long x*10 ≤Y.long): D.X i x=scaledV (D.frame i x) apex ∧ D.K i x=motion (D.frame i x) ∘ BM 1
 erm(i)(h:¬Y.D i)(x)(p:x∈ Y.band i)(u: chip (Y.u i) Y.long x*10 ≤ Y.long)(e:distant Y g B x 2): cd group (D.frame i x) (locus (D.code x)) ≤ d
 coherent(i:Y.Index)(p:Space s)(n:TAxis)(e:ClearB Y g B i p 2)(h:ClearB Y g B i (p+tstep n) 2): D.label i p=D.label i (p+tstep n)
 ground (b:Bond s)(h:Y.Vic (tag Y b.1) C.blockY (time b.1)) (e:distant Y g B b.1 2) : SU.group.chord (U b)≤d
namespace Permit
variable (L:Pad Y H C g.count.val)(P:Permit D C U g B d) {i:Y.Index}{x:Site s}(hx:x∈Y.band i)
local notation "χ" => chip (Y.u i) Y.long -- cannot `i` in notation? syntax
-- `fixed extent` licenses curvature lookup incl saturated first point
include L in
lemma shortT (h:chip (Y.u i) Y.long x ≤ C.extent+1): chip (Y.u i) Y.long x*10 ≤ Y.long:=by have ht:=L.nearP; have hp:= L.long; unfold Sized.extent at h; omega
lemma exitR (h:¬Script.stand C i x): Script.ramp C i x=1:=Rise.exit t C.stepQ _ (Nat.le_of_lt (lt_of_not_ge h)) C.up
lemma entryR (h:chip (Y.u i) Y.long x ≤ t): Script.ramp C i x=0:=Rise.enter t C.stepQ _ h C.up
include L P hx
lemma dressN (h:¬Y.D i)(p:chip (Y.u i) Y.long x ≤ C.extent+1) : D.curv C i x= rosy (D.code x) (D.frame i x) (Script.ramp C i x):=by
 by_cases v:Script.stand C i x; exact D.curvSet C i h x v; rw [exitR C v,Script.curv, if_neg (fun u=> v u.2),(P.fieldN _ h _ hx (shortT C g L p)).2]; ext1 t; exact (rosy_fuse _ _ _).symm
omit hx in
lemma curvature (x: Site s): Money (D.port C x) ∧ D.port C x 0=Pair.fullM (D.over x).val:=by
 by_cases p:dark Y x; swap; · unfold Script.over Script.port; dsimp only; simp only [p,↓reduceIte]; exact ⟨moneyT (D.code x) (dial_mem Y (gap_pick Y x p)),TG_first (D.code x) _⟩
 let i:=hr Y x; have hi: x∈Y.band i:=band_pick Y x p; rw [D.port_band C i x hi, D.over_band i x hi]; unfold Script.curv; split; swap; · exact ⟨P.money i x hi,P.begin i x hi⟩
 rename_i he; refine ⟨(moneyA (D.code x) (t:=Script.ramp C i x) (easeZ _)).pile _,?_⟩; rw [rosy0,(P.fieldN _ he.1 _ hi (shortT C g L (Nat.le_succ_of_le he.2))).1]; rfl
lemma seatM : D.port C x 2=D.K i x 2:=by
 rw [D.port_band C i _ hx]; unfold Script.curv; split_ifs with h; · rw [rosyT _ _ _ (by norm_num),(P.fieldN _ h.1 _ hx (shortT C g L (Nat.le_succ_of_le h.2))).2,Function.comp_apply,BM_1 (by norm_num)]
 rfl
lemma noVac (p:¬ Y.Vic (tag Y x) C.extent (time x)) : D.port C x=D.K i x:=by rw [D.port_band C i _ hx]; exact if_neg fun z=>p (chip_vic Y hx z.2) -- incl unused
end Permit
end YM.CF.BProof.Trek
