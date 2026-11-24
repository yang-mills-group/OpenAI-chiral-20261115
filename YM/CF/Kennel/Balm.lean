import YM.CF.Kennel.Bellis
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Kennel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m A B L:Side}{j:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
variable {e:ℝ}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{Y:Pricing j L ho (Thread j)}{V:Grasp Y B e} (M:Male)
variable (L j ho G)
def gallery : Op (Single (CSide A B)) →L[ℝ] Op (Single (CSide m B)):= pierM G (pine j L ho (Thread j) false M G 1) (pine j L ho (Thread j) true M G 1)
variable {L j ho G}
namespace Hull
variable (H:Hull j L ho a b d e n m A B G T F z Y V){U:Dress (CSide A B)}(p:relic U)
include H p
lemma breach(j':ℕ){f:Dress (CSide A B)}(h:relic f)(g:Vox m B→ Op (Single (CSide A B)))(X:Nacre.crystal j' (f∘ baby F z) g): let S:=emergence L j ho G F z M; let R:=gallery L j ho G M -- order
 Nacre.crystal j' (S (U+f)-S U) (R ∘ g):=by
 intro S R y
 let F':=𝓝[≠] (0:ℝ); let Ab(i:ℝ):=ears F z (i • y); let ℓ(i):=unionP (Ab i); let P:=foal j true M G; let B':=wh j L ho true M G; let W:=ticketT (Thread j) true M G; let Z:= ticketT (Thread j) false M G; let O:= pine j L ho (Thread j) false M G; let K:=pine j L ho (Thread j) true M G; let X'(c:Dress (CSide _ _))(t):= crux j G M (Ab t) (c (baby F z (t • y))); let α(i:ℝ):=(i^j')⁻¹
 have ht:ℓ 0=1:=by unfold ℓ Ab; rw [zero_smul,show ears F z 0=(1:nomA m A B) from Prod.ext H.native.flat link_one]; change (profile (1:Bkg _),profile (1:Bkg _))= _; simp [profile_trivial]
 have hf:= (ray_home y).mono_left (nhdsWithin_le_nhds (s:={(0:ℝ)}ᶜ)) -- wrong args
 have he:Tendsto ℓ F' (𝓝 1):=by
    rw [show 1=unionP (ears F z 0) by simpa only [ℓ,Ab,zero_smul] using ht.symm]; exact H.native.tarnish.continuousAt.tendsto.comp hf
 let jx:= (Peaks.cabin G d).mem_nhds (crests G d H.po)
 have hk:= (crown_air G (H.tape.K M _ H.fromL H.request) 1 jx).continuousAt.tendsto.comp he
 have hp:= (crown_air G (H.tape.P M _ H.fromL H.request) 1 jx).continuousAt.tendsto.comp he
 have hv:= (crown_air G (H.tape.W M _ H.fromL H.request) 1 jx).continuousAt.tendsto.comp he
 have hu:= (crown_air G (H.tape.U M _ H.fromL H.request) 1 jx).continuousAt.tendsto.comp he
 have hl:= (crown_air G (H.tape.H M _ H.fromL H.request) 1 jx).continuousAt.tendsto.comp he
 have ha:Tendsto (X' U) F' (𝓝 0):=by let hA:= H.terms M p; have hh:= hA.1.continuousAt.tendsto; rw [H.kind M p 1] at hh; exact hh.comp hf
 have hh:Tendsto (X' f) F' (𝓝 0):=by let hA:= H.terms M h; have hh:= hA.1.continuousAt.tendsto; rw [H.kind M h 1] at hh; exact hh.comp hf
 let V:= foot G (g y); let v:= (1-P 1)*V*P 1
 have ht' :∀ᶠ i in 𝓝 0, Clad (P (ℓ i)) (B' (ℓ i)) (W (ℓ i)) (Z (ℓ i)) (K (ℓ i)) ∧ Clad (1-P (ℓ i)) (1-B' (ℓ i)) (Z (ℓ i)) (W (ℓ i)) (O (ℓ i)) ∧ TagG (P (ℓ i)) (X' U i) ∧ TagG (P (ℓ i)) (X' f i):=by
    filter_upwards [(ray_home y).eventually (H.native.melod d H.po G)] with i hi; let J:= H.tape.AlongC G H.fromL H.request M (Ab i) hi
    have he : Clad _ _ _ _ _:= Peaks.court _ _ _ ho _ _ _ (J true)
    have hl:IsStarProjection (P (ℓ i)):=he.proj; refine ⟨he, ?_, tag_g _ hl, tag_g _ hl⟩ -- tune
    rw [← show foal j false M G (ℓ i)=1-P (ℓ i) from foil_neg j G true M (ℓ i),← show wh j L ho false M G (ℓ i)=1-B' (ℓ i) from wh_neg j L ho G true M (ℓ i)]; exact Peaks.court _ _ _ ho _ _ _ (J false)
 have hr:Tendsto (fun i=> α i • X' f i) F' (𝓝 v):=by
    let e:=(show Op (Single (CSide _ _))→ₗ[ℝ] Op (Iota G) from ⟨⟨foot G,fun a b=>rfl⟩,fun a b=>rfl⟩).toContinuousLinearMap; have ht : Continuous (foot G):=e.continuous
    apply ((((tendsto_const_nhds (x:=(1:Op (Iota G)))).sub hp).mul ((ht.tendsto _).comp (X y))).mul hp).congr -- tune
    intro i; change (1-P (ℓ i))*foot G (α i • (f _))*P (ℓ i) = _; rw [show foot G (α i • (f _))=α i • foot G (f (baby F z (i • y))) from rfl, Matrix.mul_smul,Matrix.smul_mul]; rfl
 have hx:=glaze (y:=0) (P∘ℓ) (B'∘ℓ) (W∘ℓ) (Z∘ℓ) (K∘ℓ) (O∘ℓ) (X' U) (X' f) α hp hu hv hk hl ha hh hr (ht'.filter_mono nhdsWithin_le_nhds)
 let T:=(show Op (Iota G)→ₗ[ℝ] Op (Single (CSide m B)) from ⟨⟨summit (patchQ G),fun a b=>rfl⟩,fun a b=>rfl⟩).toContinuousLinearMap
 have he:= (T.continuous.tendsto _).comp hx; have hV:T (star (O 1)*v*K 1)= R (g y):=by
    obtain ⟨p,h,h'⟩:=ht'.self_of_nhds
    rw [ht] at p h
    have hu:star (O 1)*(1-P 1)=star (O 1):=by rw [← show star (1-P 1)=_ from h.proj.2, ← star_mul,h.tray]
    rw [show star (O 1)*v*K 1=star (O 1)*V*K 1 by unfold v; rw [←mul_assoc,←mul_assoc,hu,mul_assoc (star _*_ ),p.tray]]; rfl
 rw [hV] at he; apply he.congr; intro i
 change T (α i • (traitP (B' _) (K _) (W _) (X' U i+ X' f i) - traitP _ _ _ (X' U i)))= α i • (S (U+f) (i • y)-S U (i • y)); rw [map_smul,map_sub]; rw [show X' U i+ X' f i=X' (U+f) i by unfold X' crux capT; rw [Pi.add_apply,foot_add,mul_add,add_mul]]; rfl
end Hull
end YM.CF.Kennel
