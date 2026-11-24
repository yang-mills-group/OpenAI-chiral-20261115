import YM.SU5.Assay.Book
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-! Join with a diagonally later sticker separated in all four axes. Diagonal chosen
 to be visible (and priced) in that order along *each* axis. -/
variable {P}{c:Option Bool}{S':Finset Cover}{f:P.Test}{l k:P.Folio}
private lemma chip {F G:Dome P.calibration → Dome P.calibration}{m:P.Folio}:
 m.transcribe (fun t=>G (F t))= (m.transcribe F).transcribe G:=by unfold Folio.transcribe; rw [List.map_map];rfl
lemma Wove.cruise (t:P.Wove c S' f l)(r:Cover)(L:List Axis):
 P.Wove c (P.placeSet S' L r) (P.cruise L r f) (l.transcribe (P.cruise L r)):=by
 induction L with
 | nil=> rw [show l.transcribe (P.cruise [] r)=l from List.map_id l];exact t
 | cons i L h=>rw [P.cruise_step];
               change P.Wove _ (plow _ _ _ (P.placeSet ..)) (P.shifts i (r i) (P.cruise L r f)) (l.transcribe (fun t=>P.shifts i (r i) (P.cruise L r t)))
               rw [chip];exact h.slide ..
variable (l k)
lemma Folio.transcribe_length (a:P.Test→P.Test):(l.transcribe a).length=l.length:=by simp only [transcribe,List.length_map]
lemma Folio.ink_length (a:ℂ):(l.ink a).length=l.length:=by simp only [ink,List.length_map]
lemma Folio.crossPrint_length :(l.crossPrint k).length=l.length*k.length:=by
 induction l with
 | nil=> simp [crossPrint]
 | cons a l h=>unfold crossPrint at h ⊢;rw [List.flatMap_cons,List.length_append,List.length_map,h,List.length_cons,add_mul,one_mul,Nat.add_comm]
variable (P)
local notation "δ0"=> ruler P.par.block
-- cf Hiro/Biltmore
lemma place_size_aux (Z:Finset Cover)(p y:Cover)(L:List Axis)(e:L.Nodup)(i:Axis)(w:y∈P.placeSet Z L p):
  ∃ t∈Z, y i=t i+if i∈L then δ0*p i else 0:=by
 induction L generalizing y with
 | nil=> exact ⟨y,w,by simp⟩
 | cons j L h=>
    obtain ⟨k,g,rfl⟩:=plow_stays K j (p j) (P.placeSet Z L p) w
    obtain ⟨t,hV,r⟩:= h _ (List.nodup_cons.mp e).2 g
    refine ⟨t,hV,?_⟩; rw [SlabMark.moves,r]
    by_cases v:i=j; · subst j;simp [show ruler (K).B=δ0 from rfl,(List.nodup_cons.mp e).1]
    simp [v]
lemma place_size (Z:Finset Cover)(p y:Cover)(i:Axis)(w:y∈P.placeSet Z Vacancy.ordinate p):∃ t∈Z, y i=t i+δ0*p i:=by
 simpa only [if_pos (Vacancy.ordinates i)] using P.place_size_aux Z p y _ Vacancy.ordinate_one i w
variable {P}{w s:ℕ}
namespace Glaze
-- spacer capacity N; offsets o, width O
abbrev pinOut (w:ℕ): ℕ:=w+w+1
abbrev pinDiagonal (w:ℕ) : Cover:=fun _=>pinOut w
abbrev pinPay (w:ℕ) :=pinOut w+w
local notation "O"=>pinPay w
local notation "o"=>pinDiagonal w
local notation "δ"=>ruler P.par.block
variable {A D:P.Glaze}(p:A.w≤w)(q:D.w≤w)
local notation "SupT"=>P.placeSet D.S Vacancy.ordinate o
lemma belt_fits (p:A.w≤w)(q:D.w≤w): P.BFits O (A.S ∪ SupT):=by
 have h:= D.fits.mono q
 refine (A.fits.mono (p.trans (Nat.le_add_left ..))).union (fun i y g=>?_)
 obtain ⟨t,u,e⟩:= P.place_size D.S _ _ i g
 have hp:= (h i t u)
 have hu: 0≤δ:= (ruler_gene ..).le
 rw [e]
 push_cast; change -δ*(↑(pinOut w)+w)+ (K).ℓ ≤ t i+δ*(pinOut w) ∧ t i+δ*(pinOut w)+(K).ℓ ≤δ*(↑(pinOut w)+w)
 have hz:0 ≤ δ * pinOut w:=mul_nonneg hu (by positivity)
 constructor <;> linarith only [hp.1,hp.2,hz]
lemma belt_pin (p:A.w≤w)(q:D.w≤w)(s:ℕ):Disjoint (P.pinFoot s A.S) (P.pinFoot s SupT):=by
 -- Glaze.distancePin
 let i:Axis:=0
 refine Set.disjoint_left.mpr ?_
 rintro z ⟨x,px,hx⟩ ⟨y,py,hy⟩
 obtain ⟨v,u,e⟩:=P.place_size _ _ _ i py
 have ux:(x i)+(K).ℓ < y i - (K).ℓ:= by
   rw [e]
   have hp: x i+ (K).ℓ ≤ δ*w:=((A.fits.mono p) i x px).2
   have hv: -δ*w+(K).ℓ ≤ v i:=((D.fits.mono q) i v u).1
   change _<v i+δ*((w+w+1:ℕ):ℤ)-_;push_cast
   linarith only [hp,hv,ruler_gene P.par.block]
 have u₁: precisionAt P.par s*((2:ℝ)•z) i -(x i:ℝ) ≤ (K).ℓ:=(abs_le.mp (hx i)).2
 have u₂: - ((K).ℓ:ℝ) ≤ precisionAt P.par s*((2:ℝ)•z) i -(y i:ℝ):=(abs_le.mp (hy i)).1
 have : (x i:ℝ) + (K).ℓ < y i - (K).ℓ:=by exact_mod_cast ux
 linarith only [u₁,u₂,this]

def belt (p:A.w≤w)(q:D.w≤w): P.Glaze:=
 { w:=pinPay w
   pos:=by unfold pinPay pinOut;omega
   «S»:=A.S∪ SupT
   F:= A.F*P.chartAll o D.F
   inlet:= Subalgebra.mul_mem (bay K _ true)
      (tallerBay K _ true Finset.subset_union_left A.inlet)
      (tallerBay K _ true Finset.subset_union_right (P.place_test _ _ _ D.inlet)) -- tune
   color:= (enclave K).mul_mem A.color (P.cruise_color _ _ D.color)
   fits:=belt_fits p q }

def beltBook (w:ℕ)(l k:P.Folio):P.Folio:=(k.transcribe (P.chartAll (pinDiagonal w))).crossPrint l
lemma belt_first (p:A.w≤w)(q:D.w≤w){g:Bool}(t:P.Wove none A.S A.F l)(z:P.FirstDress (D.apron s) g k):
 P.FirstDress ((belt p q).apron s) g (beltBook w l k):=by
 have e:=belt_pin p q s
 change _∈P.Beam s D.S g ∧ P.Wove (some g) D.S D.F k at z
 change (A.F*P.chartAll o D.F∈ P.Beam s (A.S∪ SupT) g) ∧
    P.Wove (some g) (A.S∪ SupT) (A.F*P.chartAll o D.F) (beltBook w l k)
 rw [mul_comm,Finset.union_comm]
 exact ⟨Beam.join (Beam.sail z.1 Vacancy.ordinate o) A.inlet e.symm,(Wove.cruise z.2 o Vacancy.ordinate).joint t (P.pin_disjoint _ _ _ e).symm⟩
end Glaze
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
