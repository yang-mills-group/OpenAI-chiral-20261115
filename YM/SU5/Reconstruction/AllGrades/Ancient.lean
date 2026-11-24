import YM.SU5.Reconstruction.AllGrades.Valve
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "Sc"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
local notation "K₀"=> Works Y H V G D a b P
local notation "Wq" n:max=> walkC Y H a b n
local notation "R"=>carrier Y H V G D a b P
variable (A:Impetus Y H V G D a b P)
-- one-$Epoch walk$ (=2 matter pitch) costs
section Op
include A
local notation "π" r:max n:max=> (Λ.R.L.val^(r-s)*n)
lemma projects (n:ℕ):∃ T:(Works Y H V G D a b P) →L[ℂ] (Works Y H V G D a b P), ‖T‖≤1 ∧ ∀ t≥s,∀ (x:studio (tent Y H) a 0 b), T ((Bp t) x)= (Bp t) ((Wq (π t n)) x):=by
 let q (t:ℕ) (_:t≥s):Sc→ₗ[ℂ] K₀:= (Bp t).comp (Wq (π t n)) -- notation Bp with `.comp` binder; adjust parentheses
 refine (R).bound s q (fun {t u} i j x=> ?_) 1 zero_le_one (fun t u x=>((A.backed x t (π t n)).trans_eq (one_mul _).symm))
 let W':= Wq (π t n)
 have Hq:Λ.R.L.val^(u-s)*n= Λ.R.L.val^(u-t)*(Λ.R.L.val^(t-s)*n):= by rw [← mul_assoc,← pow_add,show u-t+(t-s)=u-s by omega]
 change (Bp u) ((Wq (π u n)) (hP j x))= (Bp t) (W' x)
 rw [badges_join Y H V G D a b P j,Hq,level_walk]
 -- orientation? Goal LHS action on lift; rewrite `←level_walk ...`.
noncomputable def older (n:ℕ):=(projects Y H V G D a b s P A n).choose
local notation "E★" t:max k:max=> older Y H V G D a b t P A k
lemma old_cost (t n:ℕ):‖E★ t n‖≤1:= (projects Y H V G D a b t P A n).choose_spec.1
lemma old_pays (n:ℕ){t:ℕ}(p:s≤t)(x:Sc): (E★ s n) ((Bp t) x)=(Bp t) ((Wq (π t n)) x):= (projects Y H V G D a b s P A n).choose_spec.2 t p x
lemma old_now(n:ℕ)(x:Sc): (E★ s n) ((Bp s) x)= (Bp s) ((Wq n) x):=by rw [old_pays Y H V G D a b s P A n le_rfl,Nat.sub_self,pow_zero,one_mul]
lemma old_n (n:ℕ): 0≤ (E★ s n):=by
 let T:= E★ s n; change 0 ≤ T; apply (ContinuousLinearMap.nonneg_iff_isPositive _).2; apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp; apply (LinearMap.isPositive_iff_complex _).2; intro x
 have he:0≤ inner ℂ x (T x):=by
    apply closure_minimal (t:={x:Works Y H V G D a b P|0≤ inner ℂ x (T x)}) _ (isClosed_le continuous_const (continuous_id.inner T.continuous)) (badges_roll Y H V G D a b s P x)
    rintro x h; obtain ⟨i,h⟩:= Set.mem_iUnion.mp h; obtain ⟨y,rfl⟩:=h; change 0 ≤ inner ℂ _ ((E★ s n) _); rw [old_pays Y H V G D a b s P A n (p:=show s≤ i+s by omega)]; exact A.lit y (i+s) _
 have ht:0 ≤ inner ℂ (T x) x:=by rw [←inner_conj_symm]; simpa only [←Complex.star_def,star_nonneg_iff] using he
 exact ⟨Complex.ext rfl ht.2, ht.1⟩
lemma old_grow (n:ℕ)(t:ℕ)(p:s≤t): E★ s n= E★ t (π t n):=by
 apply badges_ext Y H V G D a b t P; intro i u x
 rw [old_pays Y H V G D a b s P A _ (p.trans u),old_pays Y H V G D a b t P A _ u,← mul_assoc (L^(i-t)),← pow_add,show i-t+(t-s)=i-s by omega]
lemma old_add(n m:ℕ): (E★ s n).comp (E★ s m)= E★ s (n+m):=by
 apply badges_ext Y H V G D a b s P; intro i u x; rw [ContinuousLinearMap.comp_apply,old_pays Y H V G D a b s P A _ u,old_pays Y H V G D a b s P A _ u,old_pays Y H V G D a b s P A _ u, walk_plus,mul_add]
lemma old_zero : E★ s 0=ContinuousLinearMap.id ℂ K₀:=by apply badges_ext Y H V G D a b s P; intro i u x; rw [old_pays Y H V G D a b s P A _ u,mul_zero,walk_root]; rfl
lemma old_close (n:ℕ): (E★ s n).adjoint= E★ s n:= IsSelfAdjoint.of_nonneg (old_n Y H V G D a b s P A n)
-- mathlib term find
lemma old_registers (x:Sc): (Bp s) x∈ ⋃ n:ℕ, Set.range (fun i:Works Y H V G D a b P=> (E★ n 2) i):=by
    -- margin δ=8 gauge after epochs. Can then drink this at height+s
    let t:=s+8; let y:=hP (show s≤t by omega) x; obtain ⟨T,u,v⟩:= atSouth Y H a b x; let Z:= volumeAround Λ l 8 T
    have q:y.val=l₀ b s 8 x.val:=by unfold y; rw [home_label,show t-s=8 by omega]
    have ht:= increase Y H s G.history.circuit a 0 T (by rw [area0]; exact v) 8
    rw [area0] at ht; have H':InTest (tent Y H) true Z b y.val:= q.symm ▸ survives Y H V s G D u 8
    let f:= C₀ a (-4) y.val; let V₁:= flow_port (tent Y H) a (-4) H'; let F:Sc:=⟨f,address a (-4) Z,V₁,by
       intro i h; obtain ⟨g,w,rfl⟩:= Finset.mem_image.mp h; rw [moves,if_pos rfl]; specialize ht g w; omega⟩ -- constructor inside Syntax `⟨f,address ... ,⟩`
    have H₂:(Wq 2) F=y:=by
       apply Subtype.ext; change C₀ a (2*(((2:ℕ)):ℤ)) (C₀ a (-4) y.val)=y.val
       rw [march_sums a b H',show 2*((2:ℕ):ℤ)+ -4=0 by norm_num,march_zero a b H']
    exact Set.mem_iUnion.mpr ⟨t,(Bp t) F,by dsimp only; rw [old_now,H₂]; exact (badges_join Y H V G D a b P _ _).symm⟩ -- notation range binder
end Op

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.old_close
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.old_grow
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.old_registers
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.old_cost
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.old_now
