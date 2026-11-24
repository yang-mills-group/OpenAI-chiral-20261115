import YM.SU5.Cordial.Horizon
import YM.SU5.Cordial.Spritz
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 8000

variable (P:Spine)(Z:Lead.Clan)
local notation "ε" => YM.basis (3:Axis)
local notation "ℓ" => P.calibration.ℓ

def phial (n:ℕ): Fin 1→Twah := fun _=>liftS (P.flash n)
lemma coast (n:ℕ) (v:0<n):
 let L:ℝ:= (ℓ:ℝ)/n
 riseX n (P.flash n).birth=L • ε + ε ∧
 riseX n (P.flash n).death= L • ε + (2:ℝ) • ε:=by
 intro L; have ht:0<(n:ℝ):=by exact_mod_cast v
 constructor
 · change riseX n (P.kernel0 n)=_
   ext j; by_cases p:j=3
   · subst j; simp [riseX,moor,kernel0,L,add_div]; exact v.ne'
   simp [kernel0,riseX,moor,p]
 ext j; by_cases p:j=3
 · subst j; simp [riseX,moor,kernel0,L,flash,add_div]; rw [div_self ht.ne']; ring
 simp [kernel0,flash,riseX,moor,p]


lemma pours: ∀ᶠ n:ℕ in atTop, Spill (P.phial n) 4 (1/2) n:=by
 filter_upwards [eventually_gt_atTop ℓ] with n t
 have u:0<n:= lt_of_le_of_lt (Nat.zero_le _) t
 let L:ℝ:= (ℓ:ℝ)/n
 let f:=nearPoints n (P.phial n)
 have he : f (0,false)=L • ε + ε ∧ f (0,true)=L • ε + (2:ℝ) • ε:= P.coast n u
 have hx:dist (f (0,true)) (f (0,false))=1:=by
    rw [dist_eq_norm,he.1,he.2,show L • ε + (2:ℝ) • ε - (L • ε + ε)=ε by module,basis_norm]
 have h: dist (L • ε) 0 ≤ 1:=by
    rw [dist_zero_right,norm_smul,basis_norm,mul_one,Real.norm_eq_abs,abs_of_nonneg (show 0≤ L by unfold L; positivity)]
    exact div_le_one_of_le₀ (by exact_mod_cast t.le) (by positivity)
 constructor
 · rintro ⟨i,b₁⟩; rw [Subsingleton.elim i (0:Fin 1)]
   change dist (f _) 0≤4
   have e:‖L • ε‖ ≤ 1:=by rwa [dist_zero_right] at h
   cases b₁
   · rw [dist_zero_right,he.1]
     have ht:=norm_add_le (L • ε) ε; rw [basis_norm] at ht; linarith only [ht,e]
   rw [dist_zero_right,he.2]
   have ht:=norm_add_le (L • ε) ((2:ℝ) • ε)
   rw [norm_smul (2:ℝ),basis_norm] at ht; norm_num at ht; linarith only [ht,e]
 rintro ⟨i,b₁⟩ ⟨j,b₂⟩; rw [Subsingleton.elim i (0:Fin 1), Subsingleton.elim j (0:Fin 1)]
 cases b₁ <;> cases b₂ <;> intro w <;> first
    | exact (w rfl).elim
    | exact (show (1:ℝ)/2≤1 by norm_num).trans_eq hx.symm
    | exact (show (1:ℝ)/2≤1 by norm_num).trans_eq (hx.symm.trans (dist_comm ..))
local notation "ch" => fun _: Fin 1=>Z
local notation "ds"=> (fun _:Fin 1=>((0:Fin 2),(0:Fin 2)))
lemma paysNine (n:ℕ)(v:0<n):
 Lead.cash false * Twah.witness (ch) [0] (nearPoints n (P.phial n)) ds = purePrice Z:=by
 let f:=nearPoints n (P.phial n)
 have he:f (0,true)-f (0,false)=ε:=by
    let L:ℝ:= (ℓ:ℝ)/n
    have h : f (0,false)=L • ε + ε ∧ f (0,true)=L • ε + (2:ℝ) • ε:= P.coast n v
    rw [h.1,h.2]; module
 rw [chorus2,lyric,Cordial.billX]
 change Lead.cash false * (numberX Z * (Onyx.pencil (f (0,true)-f (0,false)) (dnSpin 0) (upSpin 0)))=_
 rw [he,show Onyx.pencil ε _ _=P20 from k_birth,price_as]; unfold numberX; rw [show Lead.cash false=(1/5:ℂ) by simp [Lead.cash,phaseF]]; ring

def mist (n:ℕ):Papal.Weaver:=
   (P.flash n).groundWord Z - (purePrice Z:ℂ) • (1:Papal.Weaver)
lemma mist_voice (n:ℕ):
 Lamour.Bridge.Celeste.Voice (P.mist Z n) (P.flash n).patio :=
    (flourish (P.flash n) Z).sub ((Voice.one _).hushed _)
lemma mist_link (n:ℕ)(v:0<n):
 P.mist Z n= Lead.cash false • Papal.meanF
       (Twah.plait (P.phial n) (ch) [0] n)
       (Twah.witness (ch) [0] (nearPoints n (P.phial n)) ds):= by
 unfold mist Papal.meanF
 rw [smul_sub,smul_smul,P.paysNine Z n v, Designs.transferMark,
    show Twah.plait (P.phial n) (ch) [0] n=(liftS (P.flash n)).groundWord n Z from mul_one _]
 rfl
lemma mist_clarity {D:ℝ}(v:0<D) :
 ∀ᶠ n in atTop, Clarity (P.mist Z n) P.par.K.j (D/4):=by
 have j:1≤ P.par.K.j:=by rw [P.par.kJ]; decide
 filter_upwards [aroma P.par.K.j (ch) [0] ds j (D/4)
     (show 0 < (1:ℝ)/2 by norm_num) 4 (by positivity),
      P.pours,eventually_gt_atTop 0] with n y u w
 rw [P.mist_link Z n w]
 let F:=Twah.plait (P.phial n) (ch) [0] n
 let f:= Twah.witness (ch) [0] (nearPoints n (P.phial n)) ds

 refine (y _ u rfl).mono fun N t hN M x p=>?_
 have ht:= t hN M x p
 rw [Pi.smul_apply,Pi.smul_apply,map_smul,norm_smul]
 have c:‖Lead.cash false‖≤1:=by norm_num [Lead.cash,phaseF]
 exact (mul_le_mul c ht (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
