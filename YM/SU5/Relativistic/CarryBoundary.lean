import YM.SU5.Relativistic.ReadPos
import YM.SU5.Relativistic.RopeCost
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P₀" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history

variable {s n:ℕ}
local notation "μ" z:max=> gaugeShift Λ.block z
local notation "E₀" s:max f:max=> Lariat.rideL Y H T s f


namespace Lariat
section ordinary
variable {K':Calibration}
def quiet (K':Calibration) : Ink K':= ⟨1,false,∅,InTest.one⟩
def padTop (f:Lariat K' n)(r:ℕ) : Lariat K' (n+r):= match r with
 | 0=>f
 | r+1=> stretch (padTop f r) (quiet K')
def boardsPrice (n:ℕ)(X:ℕ→Finset Cover)(i:ℕ):= if i≤ n then X i else ∅
lemma hiresYear {X X':ℕ→ Finset Cover}{f:Lariat K' n}(p:Costs X f)(e:∀ i:ℕ,i≤n→X i=X' i):Costs X' f:=by induction f with| start f=> exact Eq.trans p (e 0 le_rfl)| stretch f g ih=> exact ⟨ih p.1 (fun i v=> e _ (Nat.le_succ_of_le v)),Eq.trans p.2 (e _ le_rfl)⟩
lemma better {a b:ℝ}{f:Lariat K' n}(h:f.priced (fun _=> a))(e:a≤b): f.priced (fun _=>b):= by induction f with| start f=> exact fun i x=>(h ..).trans e| stretch f g ih=> exact ⟨ih h.1,fun i x=>(h.2 ..).trans e⟩
variable (r:ℕ){f:Lariat K' n}
lemma pad_still {X:ℕ→ Finset Cover}(h:Costs X f) : Costs (boardsPrice n X) (padTop f r):=by
 induction r with
 | zero=>exact hiresYear h (fun i p=>(if_pos p).symm)
 | succ r ih=> exact ⟨ih,Eq.symm (if_neg (show ¬ n+r+1 ≤ n from by omega))⟩
lemma pad_priced {a:ℝ}(h:f.priced (fun _=> a))(p:1≤a): (padTop f r).priced (fun _=> a):=by induction r with| zero=>exact h| succ _ ih=> exact ⟨ih, fun i x=> (Tower.pay_unit i x).trans p⟩
lemma padHue (h:Lariat K' n): (padTop h r).hue=h.hue:=by induction r with| zero=>rfl| succ r ih=> change ((padTop h r).hue.xor false)=_; rw [Bool.xor_false, ih]
lemma pad_box (Λ:Preparation)(l:ℕ)(f:Lariat K' n): (padTop f r).box Λ l=volumeAround Λ l r (box Λ l f):=by induction r with| zero=>rfl| succ r ih=> change wingspan _ _ _∪∅=_; rw [union_empty, ih]; rfl
end ordinary

lemma padRides (s:ℕ)(f:Lariat K n)(r:ℕ): E₀ s (padTop f r) = stream Y H (fun s=> T s (hue f)) (s+n) r (E₀ s f):=by induction r with| zero=>rfl| succ r ih=> change T (s+(n+r)) (hue _) (E₀ s (padTop f r)) *1=_; rw [mul_one,show _=_ from padHue r f,←Nat.add_assoc,ih]; rfl
variable {k:ℕ}(m:Future Y H d k)
local notation "Z₀" m:max=> Future.kernelPath Y H d m
local notation "S₁" m:max=> Future.closing Y H d m ∪ Future.opening Y H d m
noncomputable def counter : Ink (tent Y H):=by
    have h:= Future.emit_extent Y H d m
    exact ⟨(Future.kernelPath Y H d m).val, false, (S₁ m), ((axial _ d 0 h).mono subset_union_left).mul (h.mono subset_union_right)⟩
-- boundary only put at m.t>s+n. result read at height defined by level m. ordering obvious. no definitional rec. cost uniform for varying inputs
local notation "π" n:max=> pinhole D₀ n
noncomputable def parcel (s:ℕ)(f:Lariat (tent Y H) n): Lariat (tent Y H) (n+(m.t-(s+n+1))+1) := stretch (padTop f (m.t-(s+n+1))) (Lariat.counter Y H d m)
local notation "ǫ" f:max=> parcel Y H d m s f
lemma parcel_turn (s:ℕ)(f:Lariat (tent Y H) n): hue (parcel Y H d m s f)=hue f:=by rw [parcel,hue,padHue]; exact Bool.xor_false _
lemma parcel_fac (n s:ℕ)(X:ℕ→Finset Cover)(C:ℕ) : ∃ (P:ℝ)(Z:ℕ→ Finset Cover), 0<P ∧ ∀ f:Lariat (tent Y H) n,Costs X f→priced (fun _=> (C:ℝ)) f → Costs Z (parcel Y H d m s f) ∧ priced (fun _=> P) (parcel Y H d m s f):=by
 let r:= m.t-(s+n+1); let v:=n+r+1; let t:=counter Y H d m
 obtain ⟨P₁,g⟩:= valuation Y H t.bill; let P :=max 1 (max (C:ℝ) P₁); have w:1≤P:=le_max_left ..; have y: (C:ℝ) ≤ P:= le_trans (le_max_left ..) (le_max_right ..)
 let X'(i:ℕ):=if i=v then t.S else boardsPrice n X i
 refine ⟨P,X',lt_of_lt_of_le (by norm_num) w,fun f h p=>?_⟩; have hv:Costs X' (padTop f r):= hiresYear (pad_still r h) (fun i q=> (if_neg (show i≠v from by unfold v; omega)).symm)
 exact ⟨⟨hv,(if_pos rfl).symm⟩,pad_priced r (better p y) w,fun i x=> le_trans (le_trans (g i x) (le_max_right ..)) (show max _ P₁ ≤ P from le_max_right ..)⟩
include t
lemma pad_consult (s:ℕ)(f:Lariat (tent Y H) n) (z:f.hue=false)(h:s+n < m.t) : ∃ p: TestFamily (tent Y H) true (rideL Y H T s f), E (s+(n+(m.t-(s+n+1))+1)) (rideL Y H T s (parcel Y H d m s f)) = vistaTake Y H D (pinhole (Dome (tent Y H)) (s+n) (⟨rideL Y H T s f,p⟩:Dome (tent Y H))* Future.boundary Y H d m):=by
 let R:= rideL Y H T s f
 let q:=s+n
 let p : TestFamily (tent Y H) true R:=aux_test (show InTest K true (Lariat.box Λ l f) false R from z ▸ aboard Y H u T t s f)
 let B:=(π (s+n)) (⟨R,p⟩:Dome K)
 let r:= m.t-(s+n+1); let C:= padTop f r
 have hp:s+(n+r+1)=m.t:=by unfold r; omega
 have hv:s+n+r+1=m.t:=by omega
 let A:= Future.boundary Y H d m
 have he:B∈ shorter D₀ (s+n):= short_pinhole (s+n) (⟨R,p⟩:Dome K)
 let P:=vistaFinish Y H m.t D
 have hq:P (B*A)=P B* (Z₀ m):= Decking.last (vistaDressing Y H D) (auxiliaryPad K) B m.t (climbs _ h.le he) _
 have hi:(P B).val=T (s+(n+r)) C.hue (E₀ s C):=by
    trans stream Y H G.refine (s+n) (r+1) R; swap
    · rw [←t.originally Y H V Q u (s+n) (r+1) p]; unfold C; rw [padHue,padRides,z,←Nat.add_assoc]; rfl
    have ht : (vistaFinish Y H (s+n) D B).val=R:=by unfold B vistaFinish; rw [Decking.outcrop]; rfl
    have hg := finish_upwards Y H D G (s+n) he (r+1); rw [ht,←Nat.add_assoc _ r,hv] at hg; exact hg
 refine ⟨p,?_⟩; change E _ _=vistaTake Y H D (B*A)
 rw [vistaCall Y H m.t (B*A) D ((shorter D₀ m.t).mul_mem (climbs _ h.le he) (short_pinhole m.t (Z₀ m)))]
 change E (s+(n+r+1)) (T (s+(n+r)) C.hue (E₀ s C)* (Z₀ m).val)=E m.t (P _).val; rw [hp,hq, ←hi]; rfl
end Lariat

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
