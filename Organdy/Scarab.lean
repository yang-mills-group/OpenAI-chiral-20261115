import Organdy.Ribbon
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Tulip Lat Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive  Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU
variable (s:Sweep n)
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single n
local notation "Fz"=> FC (Dwell n)


abbrev exportQ (s:Sweep n):Firing n →+* Firing n where
  toFun v:=fun x=>roll s (v (yellA s⁻¹ x))
  map_one':= funext fun _=> map_one (roll s)
  map_zero':= funext fun _=>map_zero (roll s)
  map_add' _ _:=funext fun _=>map_add (roll s) _ _
  map_mul' _ _:=funext fun _=>map_mul (roll s) _ _

variable {X Y:Aura n}{Z D:Support (More n)}
local notation "✂"=> exportQ s
local notation "allA"=> moldA s
local notation "Ss"=>actY s
attribute [local instance] loreM loreN

lemma lightsB (V:Pane n)(pV:V∈σX p (allA X) (Ss Z)):
   flashA s⁻¹ V ∈ σX p X Z:=by
   simpa only [show (moldA s X).val=Ss X.val from rfl,tape_C] using
     ((Salt.lights_C («T»:=s⁻¹) ..).mpr pV)

abbrev flick (s:Sweep n) (g:Seat n→E):Seat n→E:=
   ((polarT s.charge ∘g) ∘ (castX s).anon n)

lemma flick_veil (g:Seat n→E):
   flick s (flick s⁻¹ g)= g:=by
   have hz : (s⁻¹).charge=s.charge:=rfl
   funext i
   change polarT s.charge (polarT (s⁻¹).charge (g (boxA s⁻¹ (boxA s i))))=_
   rw [hz, polar_t, Bool.xor_self,sitU,Equiv.symm_apply_apply]
   rfl

lemma flick_rev (V:Orbit n) (g:Seat n→E):
   yellA s (Lattice.gauge g V.1, threadG g V.2)=
    (Lattice.gauge (flick s g) (flashA s V.1),threadG (flick s g) (bun s V.2)):=by
    unfold flick
    refine Prod.ext (revG ..) (funext fun i=> ?_); change bun s (threadG g V.2) i= threadG _ (bun s V.2) i; simp only [bun,man,threadG,map_mul,map_inv];rfl

lemma rollingMeas : Measurable (roll s) :=
    -- adapt to loreM
   (tour_c (s.charge.xor D₁) false (praise s)).measurable

lemma packing {m:Firing n}
    (u:Crate p X D Y m):
    Crate p (allA X) (Ss D) (allA Y) (✂ m) :=by
   let f:=yellA s⁻¹
   have per:Measurable f:= ((revM s⁻¹).measurable.comp measurable_fst).prodMk ((tuft s⁻¹).measurable.comp measurable_snd)
   refine ⟨(rollingMeas s).comp (u.cog.comp per),
      fun i=>blanket s (u.body _),fun i j b c a d=> ?_,fun i g hi=>?_⟩
   · obtain ⟨t,v⟩:=yellow s⁻¹ i j (Ss X.val) a d
     rw [tape_C] at t v
     exact congrArg (roll s) (u.same _ _ (lightsB s i.1 b) (lightsB s j.1 c) t v)

   change roll s (m (yellA s⁻¹ (Lattice.gauge _ _,threadG _ _)))= lotY false false (tradew n g) _
   rw [flick_rev]
   let g':=flick s⁻¹ g
   let z:=yellA s⁻¹ i
   change roll s (m (Lattice.gauge g' z.1,threadG g' z.2))= lotY false false (tradew n g) (roll s (m z))
   rw [u.gauge z g' (lightsB s i.1 hi)]
   have hx:=yum s g' (u.body z)
   change _=lotY false false (tradew n (flick s g')) _ at hx
   rw [flick_veil] at hx
   exact hx

open Jet
local notation "Ω"=> Orbit n
abbrev uplift (k:ℕ) := (composeCost k 1 1)*Tenant.quota^2
lemma uplift_nn (k:ℕ):0 ≤ uplift k:=by unfold uplift composeCost; positivity

open Drapes Branch
variable {t u v w:ℝ}{S:Support (More n)}{L:Scree.Loom n}{F:Raw (Openc (More n) d) (Single n)}
    {C:Toll (Single n)} -- check
open Drapes Jet Branch
lemma reprice
   (f:Roof n t d q L) (x:0<d)
   (Jf:Op JS→Fz)(U:JS→ JS → Fz)
   (j:Suite (badge _) (bail n d) (bail n d) S C F)
   (φ:Glyph Jf U h)(φ':Spinner h U)
   (y:p.threshold ≤ t)(z:HopeT d v w p.order) (k:p.threshold ≤ w)
   (b0:cipherK q ≤ 5*p.B)(b1:3 ≤ p.B)
   (g:halo (q+10) S ⊆ Y.val):
   Herb p q (allA Y) h (✂ (Glyph.cure Jf f x F)) (uplift p.order * Glyph.vest p h C):=by
   let M:=Glyph.cure Jf f x F
   have old:=Herb.kernelR f x Jf U j φ y z k b0 b1 g
   refine ⟨mul_nonneg (uplift_nn _) old.price,?_,?_⟩

   swap
   · intro X' b i hi j₀
     obtain ⟨X,rfl⟩:= (allA).surjective X'
     have e:Y.val⊆X.val:=map_subset_map.mp b
     exact congrArg (roll s)
       (old.clean X e (yellA s⁻¹ i)
         (lightsB (Z:=∅) s i.1 (by simpa only [actY,map_empty] using hi)) (bun s⁻¹ j₀))

   intro X' a D' _ c
   obtain ⟨X,rfl⟩:=(allA).surjective X'
   have hd :∃ D,Ss D=D':=⟨actY s⁻¹ D',by simpa only [inv_inv] using tape_C s⁻¹ D'⟩
   obtain ⟨D,rfl⟩:=hd
   have e:Y.val⊆X.val:=map_subset_map.mp a
   have he: halo (cipherK q) D ⊆ X.val:=by
      have hn: halo (cipherK q) (Ss D)=Ss (halo (cipherK q) D):=by
         unfold Salt.actY; rw [←sitU,paysT]
      rw [hn] at c;exact map_subset_map.mp c

   refine ⟨packing s (Glyph.horn φ f x j y he g e),?_⟩
   apply AuraOp.pay
   let χ:ℂ→ℂ := cSignX (s.charge.xor D₁)
   let K(i l:JS)(V':Orbit n):=χ (F (roller x f (yellA s⁻¹ V')) i l)
   let J(i l:JS)(V':Orbit n):=K i l V' • roll s (U i l)

   let A(i l:JS):=composeCost p.order (C i l) 1
   let W(i l:JS):=((p.order+1:ℝ)*A i l)*(Tenant.quota^2*h^2)
   have hu(i l:JS) : AuraOp p (allA X) (Ss D) (J i l) h (W i l):=by
     have hA:A i l ≥0:=by have hn:=j.nonn i l; unfold A composeCost; positivity
     apply AuraOp.sat h (K i l) (roll s (U i l))
       (φ' s i l) (mul_nonneg (by positivity) hA)
     intro V b Z nz
     let Z':= actY s⁻¹ Z
     have eD:D⊆Z':=by
        unfold Z';nth_rw 1 [←tape_C s D];exact map_subset_map.mpr nz
     let fP(w:tangD n):=F (roller x f
         (pressQ p Z' (flashA s⁻¹ V.1) w,(yellA s⁻¹ V).2)) i l
     let Q:=door_b s⁻¹ V.1
     have hw:‖Q‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun j=> by
        rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
          fun z=> (cod_E s⁻¹ V.1 j z).trans_le (norm_le_pi_norm ..)
     let E(t:tangD n):=K i l (pressQ p Z V.1 t,V.2)
     have hx: Allows p.order fP (Q 0) (C i l):=by
       rw [map_zero];exact earn_b x f y j z (yellA s⁻¹ V) X (g.trans e) k he b0 b1 (lightsB s V.1 b) eD _ _
     have hr:=hx.comp (allows_linear hw

       (show ‖Q 0‖ ≤ 1 from by rw [map_zero,norm_zero];exact zero_le_one))
     apply bare_p _ (A i l)
     have hE:E=cast_B (s.charge.xor D₁) ∘ (fP ∘ Q):=by
        funext t
        unfold E K χ fP yellA;rw [parl_v,←castT]; rfl
     change Allows _ E 0 _
     rw [hE,←one_mul (A i l)]
     exact hr.linear _ (cap_X _)
   have hd: ✂ M=∑i:JS,∑l:JS, J i l:=by
      funext V
      change roll s (Jf _)=_
      rw [φ.whirl];simp_rw [Finset.sum_apply,map_sum]
      apply sum_congr rfl;intro i _;apply sum_congr rfl;intro l _
      exact Ione.G_lot ..
   have hx: uplift p.order * Glyph.vest p h C=∑i:JS,∑l:JS,W i l:=by
      unfold W A Glyph.vest uplift composeCost ledgerV
      simp only [sum_mul,mul_sum]
      apply sum_congr rfl;intro i _;apply sum_congr rfl;intro l _;ring
   rw [show Glyph.cure Jf f x F=M from rfl,hd,hx]
   exact AuraOp.sumR _ _ _ _ fun i _=>AuraOp.sumR _ _ _ _ fun l _=>hu ..
end YM.CF.Organdy
