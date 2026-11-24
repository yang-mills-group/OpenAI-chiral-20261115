import WakeRoad.Twilight
import WakeRoad.Vote
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
open Dial Pressure
open Stationary (Gaia)
set_option quotPrecheck false
open Onyx
lemma sum_seals {α ε:Type*}[Fintype α][AddCommMonoid ε]{m n:ℕ}(f:(Fin (m+n)→α)→ε): (∑ i,f i)=∑ i:Fin m→α,∑ j:Fin n→α,f (Fin.append i j) := by
 rw [←Equiv.sum_comp (Fin.appendEquiv m n) f,Fintype.sum_prod_type]; rfl
variable {m n:ℕ}
local notation "iA"=> @Fin.castAdd m n
private abbrev duo := SU.Slot × SU.Slot
private abbrev splash {m n:ℕ}(z:Fin m→Fin n)(q:Picture m): Picture n:=(z q.1,q.2)
lemma ribbon_joint (f:Fin m→duo)(g:Fin n→duo): ribbonCast (Fin.append f g)=(ribbonCast f).map (splash iA)++(ribbonCast g).map (splash (fun i:Fin n=> Fin.natAdd m i)):=by
 let Q{k:ℕ}(t:Fin k→duo)(i:Fin k): List (Picture k):=[(i,(t i).2,true),(i,(t i).1,false)]
 let U:= Fin.append f g; let b:= fun i:Fin n=> Fin.natAdd m i
 have he: Q U=Fin.append ((List.map (splash iA)) ∘ (Q f)) (List.map (splash b) ∘ (Q g)):=by
    funext i; cases i using Fin.addCases with
    | left i=> unfold U Q; rw [Fin.append_left,Fin.append_left]; rfl
    | right i=> unfold U Q; rw [Fin.append_right,Fin.append_right]; rfl
 change (List.ofFn (Q U)).flatten= (List.ofFn (Q f)).flatten.map (splash iA)++(List.ofFn (Q g)).flatten.map (splash b)
 rw [he,List.ofFn_fin_append,List.flatten_append, List.map_flatten,List.map_flatten,List.map_ofFn,List.map_ofFn]

lemma spin_joint (f:Fin m→Op SU.Slot)(g:Fin n→ Op SU.Slot)(F:Picture (m+n)→Picture (m+n)→ℂ)(p:Picture m→Picture m→ℂ)(q:Picture n→Picture n→ℂ)
    (h:∀ i j,p i j=F (splash iA i) (splash iA j))(u:∀ i j,q i j = F (splash (Fin.natAdd m) i) (splash (Fin.natAdd m) j))(e:∀ i j,F (splash iA i) (splash (Fin.natAdd m) j)=0): spinFilm (m+n) (Fin.append f g) F=spinFilm m f p * spinFilm n g q:=by
 unfold spinFilm; rw [sum_seals,sum_mul]; refine sum_congr rfl fun i _=>?_ ; rw [mul_sum]; refine sum_congr rfl fun j _=>?_
 rw [ribbon_joint,rune_divide]
 · rw [rune_map p _ _ F h,rune_map q _ _ F u,Fin.prod_univ_add]; simp_rw [Fin.append_left,Fin.append_right]; ring
 rintro k hk t ht; obtain ⟨k,hk,rfl⟩:= List.mem_map.mp hk; obtain ⟨t,ht,rfl⟩:= List.mem_map.mp ht; exact e k t

open Maxwell (Free.Pole)
variable (P:Fin m→Gaia)(H:Fin n→Gaia)(p:ℕ→Fin m→ Gaia)(q:ℕ→Fin n→ Gaia)
variable (hp:∀ k i j,p k i-p k j=P i-P j)(hq:∀ k i j, q k i-q k j=H i-H j)(h:∀ i j,Tendsto (fun k=> ‖p k i-q k j‖) atTop atTop)
local notation "WZ" k:max=> Fin.append (p k) (q k)
include hp hq h
private def limit_zero (P: Fin m→ Gaia)(H:Fin n→ Gaia) (i j: Fin (m+n)) : ℂ:= Fin.addCases (fun i=> Fin.addCases (fun a=> shotL (P i-P a) 0 0) (fun _=>0) j) (fun j'=>Fin.addCases (fun _=>0) (fun a=>shotL (H j'-H a) 0 0) j) i
lemma credits_zero(i j: Picture (m+n)): Tendsto (fun k=> spinOrbit (WZ k) 0 i j) atTop (𝓝 (postD (limit_zero P H) i j)):= post_moves _ _ (fun a b=>by
 cases a using Fin.addCases <;> cases b using Fin.addCases
 · simp only [limit_zero,Fin.append_left,Fin.addCases_left,hp]; exact tendsto_const_nhds
 · next i j=> simp only [limit_zero,Fin.append_left,Fin.append_right,Fin.addCases_right,Fin.addCases_left]; exact kP_further _ (h i j)
 · next i j=>
    simp only [limit_zero,Fin.append_left,Fin.append_right,Fin.addCases_right,Fin.addCases_left]; refine kP_further _ ((h j i).congr (fun _=> norm_sub_rev ..))
 simp only [limit_zero,Fin.append_right,Fin.addCases_right,hq]; exact tendsto_const_nhds) i j
lemma spin_factor (a:swatches m)(b:swatches n) : Tendsto (fun k=>Hearth.schedule (Fin.append a b) (WZ k) 0) atTop (𝓝 (Hearth.schedule a P 0 * Hearth.schedule b H 0)):=by
 let f(i:Fin m):=walkC (tintM (a i)); let g(i:Fin n):=walkC (tintM (b i)); let G:= postD (limit_zero P H);
 have ht:= spin_moves (Fin.append f g) _ _ (credits_zero P H p q hp hq h);
 have H': spinFilm (m+n) (Fin.append f g) G=spinFilm m f (spinOrbit P 0)*spinFilm n g (spinOrbit H 0):= spin_joint f g G _ _ (fun i j=>?_ ) (fun i j=>?_ ) (fun i j=>?_)
 · rw [H'] at ht; refine ht.congr fun x=>?_
   change spinFilm _ _ _ =spinFilm _ _ _; congr 1; funext i
   cases i using Fin.addCases with
   | left i=> simp only [Fin.append_left]; rfl
   | right i=> simp only [Fin.append_right]; rfl
 · unfold G splash postD spinOrbit; simp only [limit_zero,Fin.addCases_left]; rfl
 · unfold G splash postD spinOrbit; simp only [limit_zero,Fin.addCases_right]; rfl
 unfold G splash postD; simp [limit_zero]; -- split unnecessary
omit hp hq h
lemma lightRun (A B:PlaqAxes){x:ℕ→ Gaia}(h:Tendsto (fun i=> ‖x i‖) atTop atTop): Tendsto (fun k=> Regis.Circuit.specter A B (x k)) atTop (𝓝 0):= by
 obtain ⟨C,hp,t⟩:= (Maxwell.Free.bare_pole A.val.1 A.val.2 B.val.1 B.val.2).bounds
 have ht:Tendsto (fun i=> ‖x i‖⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp h
 let Q:= Maxwell.bareCurl A.val.1 A.val.2 B.val.1 B.val.2
 have hv:Tendsto (fun i=> Q (x i)) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ((h.eventually_gt_atTop 0).mono (fun i x=> t _ (norm_pos_iff.mp x))) (show Tendsto (fun i=> C* ‖x i‖⁻¹^4) atTop (𝓝 0) by simpa only [zero_pow (by decide:(4:ℕ)≠0),mul_zero] using ((ht.pow 4).const_mul C)))
 exact (Complex.ofReal_zero ▸ Complex.continuous_ofReal.continuousAt.tendsto.comp hv) -- ▸ ? infer
lemma glaze_factor (P H:Fin 2→Gaia)(p q:ℕ→ Fin 2→ Gaia)(F D: Fin 2→ PlaqAxes)(a b:swatches 2)
    (hp:∀ k i j,p k i-p k j=P i-P j)(hq:∀ k i j,q k i-q k j=H i-H j)(h:∀ i j, Tendsto (fun k=> ‖p k i-q k j‖) atTop atTop): Tendsto (fun k=> wickTranche (fun i j=> hardCoin (Fin.append (p k) (q k)) (Fin.append F D) i j (Fin.append a b i) (Fin.append a b j))) atTop (𝓝 (hardCoin P F (0:Fin 2) 1 (a 0) (a 1)*hardCoin H D (0:Fin 2) 1 (b 0) (b 1))) := by
 let v:=Fin.castAdd (n:=2) 2; let z':Fin 2→Fin 4:=Fin.natAdd 2; let Z:=fun k=>Fin.append (p k) (q k); let X:=Fin.append F D; let u:=Fin.append a b
 let M(k i j):=hardCoin (Z k) X i j (u i) (u j)
 have he(i j:Fin 2): Tendsto (fun k=>M k (v i) (v j)) atTop (𝓝 (hardCoin P F i j (a i) (a j))):=by unfold M hardCoin Z X u v; simp_rw [Fin.append_left,hp]; exact tendsto_const_nhds
 have hv(i j:Fin 2): Tendsto (fun k=>M k (z' i) (z' j)) atTop (𝓝 (hardCoin H D i j (b i) (b j))):=by unfold M hardCoin Z X u z'; simp_rw [Fin.append_right,hq]; exact tendsto_const_nhds
 have hu(i j:Fin 2): Tendsto (fun k=>M k (v i) (z' j)) atTop (𝓝 0):=by
    unfold M hardCoin Z X u v z'; simp_rw [Fin.append_left,Fin.append_right]; simpa only [mul_zero] using (lightRun (F i) (D j) (h i j)).const_mul (↑(sch (G:=SU.group) (a i) (b j)):ℂ)
 have hf:=((((he 0 1).mul (hv 0 1)).add ((hu 0 0).mul (hu 1 1))).add ((hu 0 1).mul (hu 1 0))); rw [mul_zero,add_zero,add_zero] at hf -- rw one instance mul_zero?
 exact hf
lemma gala_factor (P H:Fin 2→Gaia)(p q:ℕ→ Fin 2→ Gaia)(F D: Fin 2→ PlaqAxes)
    (hp:∀ k i j,p k i-p k j=P i-P j)(hq:∀ k i j,q k i-q k j=H i-H j)(h:∀ i j, Tendsto (fun k=> ‖p k i-q k j‖) atTop atTop): Tendsto (fun k=> galaTarget (Fin.append (p k) (q k)) 0 (Fin.append F D)) atTop (𝓝 (duoTarget P 0 F*duoTarget H 0 D)):=by
 let X(k):=Fin.append (p k) (q k)
 let f(k)(a b:swatches 2):=wickTranche (fun i j=>hardCoin (X k) (Fin.append F D) i j ((Fin.append a b) i) ((Fin.append a b) j))* Hearth.schedule (Fin.append a b) (X k) 0
 let v(a:swatches 2):= hardCoin P F (0:Fin 2) 1 (a 0) (a 1)* Hearth.schedule a P 0; let w(b:swatches 2):= hardCoin H D (0:Fin 2) 1 (b 0) (b 1)*Hearth.schedule b H 0
 have he(a b:swatches 2) : Tendsto (fun k=> f k a b) atTop (𝓝 (v a*w b)):=by
    let ht:= (glaze_factor P H p q F D a b hp hq h).mul (spin_factor P H p q hp hq h a b); unfold v w; rw [show hardCoin _ _ _ _ (a 0) (a 1)*Hearth.schedule _ _ _ * (_*Hearth.schedule b _ _)= _ from mul_mul_mul_comm ..]; exact ht
 have ht:=tendsto_finsetSum (univ:Finset (swatches 2)) (fun i _=> tendsto_finsetSum (univ:Finset (swatches 2)) (fun j _=> he i j)); simp_rw [←mul_sum] at ht; rw [←sum_mul] at ht
 refine ht.congr fun k=> (sum_seals (m:=2) (n:=2) _).symm
#print axioms gala_factor
end GramSignal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
