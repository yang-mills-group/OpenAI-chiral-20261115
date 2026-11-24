import Merino.Plume.Runners
import Merino.Silk.Keeps
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3500
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Plume
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Skye Scree Vale RG
open Py (hueW stemS pinpr)
variable (P:Spine)


open Cuff Hem Medal Lace
open Buffered Lifted Afterglow Journey Tower Tower.SlabMark

abbrev wall (s t:ℕ):=vale (etch P s) (Lace.noon t)
abbrev half (s t:ℕ)(f:LinksC→ℂ):=
 present P.calibration (chaste (Lace.noon t) (clearM P s) f)
abbrev both (s t:ℕ)(f:LinksC→ℂ):=
  mirror P.calibration pole 0 (half P s t f)*half P s t f
variable {s:ℕ}{F:ℕ→LinksC→ℂ}{f:LinksC→ℂ}{b:ℝ}
lemma Plump.stillHalf (z:Plump (Lattice.box (etch P s)) b F f)(t:ℕ):
 BQueue (wall P s t) (fun i=>half P s t (F i)) (half P s t f):=
  (z.rampC (Lace.noon t) (clearM P s)).rides P.calibration

open scoped InnerProductSpace


/-- Reading at a native volume, without the cast. -/
abbrev glance (n:Side)(t:ℕ)(c:ℝ)(f:LinksC→ℂ):=
   staged t c (pstar (f∘onC n))
lemma half_glance(s t:ℕ)(f:LinksC→ℂ)(m:Lattice.Side):
 half P s t f m=glance (P.calibration.c m) t (clearM P s) f:=by
 funext x
 simp only [half,present,scalar,Function.comp_apply,chaste_period,glance,staged,Pi.smul_apply,
    icon,now,smul_smul]

lemma both_consults (s t i k:ℕ)(f:LinksC→ℂ):
 sharp P.run P.large s i k (both P s t f)=compass P.run i k s
   (photo (glance (RegNum P s i) t (clearM P s) f)):=by
 have he{m n:Side}(g:m=n): (g ▸ photo (glance m t (clearM P s) f) :Mark n)
    = photo (glance n t (clearM P s) f):=by subst n; rfl
 unfold sharp Journey.listen
 congr 1 -- careful
 unfold send
 simp only [both,Pi.mul_apply,Tower.mirror,half_glance]
 exact he _ 


lemma combined (z:Plump (Lattice.box (etch P s)) b F f)(t:ℕ){r:ℕ→ℕ}(l:StrictMono r):
   Tendsto (fun i=>compass P.run (P.nomadic (r i)) (P.engine (r i)) s
      (photo (glance (RegNum P s (P.nomadic (r i))) t (clearM P s) (F i)))) atTop (𝓝 (P.E s (both P s t f))):=by
 have h:=z.stillHalf P t
 have g:=(BQueue.revolve pole 0 h).multiply h
 simp_rw [←both_consults]
 exact merino_coffee P.run P.large s P.history P.law r l.tendsto_atTop g




def Way (s t:ℕ):Prop:= etch P s + P.calibration.ℓ ≤ t
lemma clears:
 ∀ᶠ s in atTop,∀ t,Strut (scaleM P s) t → Way P s t:=by
 filter_upwards [(turnover P.par).eventually (offPeak P.calibration.ℓ)] with s p t c
 let u:=etch P s+P.calibration.ℓ
 have h:(2*u+4)^2 ≤ t:=p t c
 exact le_trans (show u≤_ by nlinarith) h
variable {t:ℕ}
lemma opens (h:Way P s t):
 region pole 0 P.calibration.ℓ (wall P s t):=by
 unfold Way at h
 intro i k
 obtain ⟨j,v,rfl⟩:=mem_image.mp k
 have x: Lace.noon t pole=t:=by simp [Lace.noon]
 rw [Pi.add_apply,x]
 have y:=(box_test.mp v).1 pole
 omega

/-- A moving-plane vector in the unselected tower, same Spine.room.
Singlet is paid as well. -/
lemma entering (h:Way P s t)(g:Swan (Lattice.box (etch P s)) b f):
 half P s t f ∈ P.Vox pole s∧ CovCover P.calibration (half P s t f):=by
 have h₁:=g.rampC (Lace.noon t) (clearM P s)
 refine ⟨(purpose_ok ..).mpr ⟨⟨wall P s t,h₁.law P.calibration,by rw [area0]; exact opens P h⟩,
       fun v=>by cases v⟩,?_⟩
 intro m u x
 have w:=sang_full h₁.sang (P.calibration.c m) u x.1
 unfold half present scalar
 simp only [ simultaneous,Prod.map_fst,Fock.twist_scalar,map_one]
 exact congrArg (· • 1) w


lemma vocal (V:P.Vox pole s)(v:V.val = half P s t f):
 (P.E s (both P s t f)).re= ‖P.piece pole s V‖^2:=by
 rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
 have q:=contracts P.run P.large P.law P.history.circuit pole 0 false (P.room pole)
      s s s le_rfl le_rfl V V
 rw [area0,Nat.sub_self,v] at q
 exact congrArg Complex.re q.symm

end YM.CF.Merino.Plume
