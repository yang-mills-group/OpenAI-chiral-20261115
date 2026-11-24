import YM.SU5.FiniteGaugeData.Stent.Ound
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
section
open Tint
-- local genuine raw vs working mask.Assemb at support all.
variable (K:Calibration)(R:Patch)
variable {S T:Finset Cover}
structure Anorak (S:Finset Cover)(F:LinksC→ℂ) :Prop where
  walk:GaugeInvariant F
  continuous: Continuous F
  loc : Lattice.LocalOn S F
variable (F:LinksC→ℂ)(P:Anorak S F)(b:Bool)
def shiftW {S:Finset Cover} (F:LinksC→ℂ)(P:Anorak S F) (U: PairsC): ℂ:= if b then F U.2 else F U.1 -- b before F
lemma shift_loc : Coeff true S (shiftW b F P):= by cases b; exact Coeff.fromC _ _ P.continuous P.loc; exact ⟨fun _=> by contradiction, Env.compact (P.continuous.comp continuous_snd), fun x y _ v => P.loc x.2 y.2 v⟩ -- Σ width
private lemma shift_dur : Durable K (scalar K (shiftW b F P)):=by
 cases b
 · exact roseColor F P.walk K
 intro m g x; change F (onC (K.c m) (Lattice.gauge g x.2)) • (1:FC _) = twist _ (F (onC _ x.2) • 1); rw [twist_scalar,map_one,Chart.gauge_here,P.walk] -- g action
noncomputable def shunt (K:Calibration)(b:Bool)(F:LinksC→ℂ)(P:Anorak S F) : W K:= ⟨scalar K (shiftW b F P),⟨⟨S,.seed (shift_loc ..)⟩,by simp⟩,(show Durable _ _ from shift_dur K F P b)⟩ -- basic proof(_, list)
lemma loc_shunt(K:Calibration) : Locator K (shunt K b F P) S:= InTest.seed (shift_loc ..)
lemma shunt_narrow : InTest K false S false (shunt K false F P).val:= .seed (.fromC _ _ P.continuous P.loc)
lemma sold_shunt (h:Real.exp 1≤Λ.x)(s i:ℕ) : sold Y h s i (shunt (tent Y h) b F P).val = fun V=> (if b then F (onC _ V.2) else F (onC _ V.1)) • 1:=by unfold sold; exact castT F b (terrain Y h (Y.ir i) s)
where castT(F':LinksC→ℂ)(b:Bool){N P:Side}(h:N=P): ship h ((fun W:Fields N=>(if b then F' (onC _ W.2) else F' (onC _ W.1)) • 1):Mark N)=fun W:Fields P=>(if b then F' (onC _ W.2) else F' (onC _ W.1)) • 1:=by subst P; rfl
-- Physical reader coefficient labels are continuous centered finite Borel. Include multiplication and wider layers.
lemma Anorak.widen (P:Anorak S F)(h:S⊆T): Anorak T F:= ⟨P.walk,P.continuous,fun U V u=>P.loc _ _ (fun i s v => u i (h s) (h v))⟩
lemma Anorak.more{S T:Finset Cover}{F F': LinksC→ℂ} (p:Anorak S F)(q:Anorak T F'): Anorak (S∪T) (F*F'):=⟨fun t y=>congrArg₂ (·*·) (p.walk ..) (q.walk ..),p.continuous.mul q.continuous,fun U V e=>congrArg₂ (·*·) (p.loc _ _ (fun i s v=> e i (mem_union_left _ s) (mem_union_left _ v))) (q.loc _ _ (fun i s v=> e i (mem_union_right _ s) (mem_union_right _ v))) ⟩
lemma Anorak.moreHere {S:Finset Cover}{F F': LinksC→ℂ} (p:Anorak S F)(q:Anorak S F'): Anorak S (F*F'):= by nth_rw 1 [← Finset.union_idempotent S]; exact p.more q
include P in
lemma Anorak.paint (q:ℂ→ℂ)(h:Continuous q): Anorak S (q∘ F):= ⟨fun t y=>congrArg q (P.walk ..), h.comp P.continuous, fun U V e=> congrArg q (P.loc U V e) ⟩ -- forgot include P
lemma shunt_more {F:LinksC→ℂ}(F':LinksC→ℂ)(P:Anorak S F)(Q:Anorak T F'): shunt K b (F*F') (P.more Q)= shunt K b F P*shunt K b F' Q:=by apply Subtype.ext; funext m x; cases b <;> (unfold shunt shiftW; change ((_:ℂ)*(_:ℂ)) • (1:FC (Single (K.c m))) = ((_:ℂ) • (1:FC (Single (K.c m))))*((_:ℂ) • (1:FC (Single (K.c m)))); rw [←smul_smul, Algebra.smul_mul_assoc,one_mul]; rfl); -- tune metavars
lemma shunt_same {F F':LinksC→ℂ}{P:Anorak S F}{P':Anorak T F'} (p:F=F'): shunt K b F P= shunt K b F' P':=by subst F'; rfl
variable (A:Finset (Face ℤ))(r:ℝ)
lemma healCare : Anorak (carpet A) (bedH A r):= ⟨bedColour A r, bedH_cont .., bedH_local A r⟩
-- C static geometry; no extra limit.
include P
omit P
lemma Pace.cont: Continuous (PaceLock R):=by unfold PaceLock; exact (continuous_const.mul (Poleg (b:=true) 0).matrix_det).mul (continuous_const.mul (Poleg (b:=false) 2).matrix_det).star
variable (t:4≤R.L.val)
include t in
lemma Pace.money (p:Op SU.Slot):PaceLock R p≠0:=by
 have hp(i)(b:Bool): (Lock p b i).det ≠0:= isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (lock_live ..)); unfold PaceLock; have hg:0<(Bliss R).re:=bliss_pay R t; have hz:Bliss R^ (Fintype.card SU.Slot) ≠0:= pow_ne_zero _ (fun p=> hg.ne' (by rw [p]; rfl)); exact mul_ne_zero (mul_ne_zero hz (hp 0 true)) (by simpa using (mul_ne_zero hz (hp 2 false))) -- include t need
-- Nylon determinant.
lemma Nylon.cont : Continuous (Nylon R):=by
 have he:Continuous (Louvre R):= (continuous_const (y:=(Fintype.card Lattice.Order:ℝ)⁻¹)).smul (continuous_finsetSum univ fun i _=>SU.matter_cont.comp (Wilson.continuous_travel (growAge i) (nodeC (specialM R.L))))
 exact he.matrix_det.mul he.matrix_det.star -- tune
include t
lemma Nylon.loc : Lattice.LocalOn (fieldQ R.L) (Nylon R):=by
 intro U V u; suffices h: Louvre R U=Louvre R V by unfold Nylon; rw [h]
 let G:Ratio 1 R.L:=⟨R.L,by simp⟩; unfold Louvre; apply congrArg; refine sum_congr rfl (fun j _=>?_ ); let W:= visits (nodeC (specialM R.L)) (growAge j); have he: W.toFinset⊆fieldQ R.L:= forge G R.odd_side t j; exact congrArg (fun U:SU.E=> (matter U).val) (travel_local (nodeC (specialM R.L)) (growAge j) _ _ (fun i h k=> u i (he (List.mem_toFinset.mpr h)) (he (List.mem_toFinset.mpr k))))
omit t
lemma Nylon.walk : GaugeInvariant (Nylon R):=by
 intro T U; let z:= matter (T (nodeC (specialM R.L))); let v:= matter ((T (zeroL R.L))⁻¹); have h: Louvre R (gauge T U)= z.val* Louvre R U*v.val:=by
    unfold Louvre; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_sum,sum_mul]; unfold Shadow; refine congrArg _ (sum_congr rfl (fun i e=>?_)); rw [travel_gauge,Buffered.Stent.tail _ i R.odd_side,map_mul,map_mul]; rfl
 unfold Nylon; rw [h,Matrix.det_mul,Matrix.det_mul, show z.val.det=1 from triple_det _,show v.val.det=1 from triple_det _, one_mul,mul_one]
lemma locketA (t:4≤R.L.val) : Anorak (fieldQ R.L) (Nylon R):=⟨Nylon.walk R,Nylon.cont R,Nylon.loc R t⟩
#print axioms locketA
#print axioms shunt_narrow
end
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
