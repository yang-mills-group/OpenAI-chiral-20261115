import YM.SU5.FiniteGaugeData.Marked.Variation.Vitrine

/-! # Hospital. Read off canonical coefficients at a roomy period. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry
attribute [local instance] opCStarAlgebra
variable (S:Finset Cover)(N:Side)

structure Hosp : Prop where
 seat_ : Set.InjOn (wrap (More N)) S

def occupy (h:Hosp S N):Tag S↪ Single N:=
 { toFun:=fun i=> Lifted.index N (who S i).1 (who S i).2.1 (who S i).2.2
   inj':=by
    rintro ⟨⟨x,i,j⟩,p⟩ ⟨⟨y,k,l⟩,q⟩ t
    change ((wrap N x,i),j)=((wrap N y,k),l) at t
    have he:x=y:= by apply nodeC_inj; apply h.seat_ p q; rw [←node_of,←node_of]; exact congrArg node (congrArg (fun v=>v.1.1) t)
    obtain rfl:=he
    cases congrArg (fun v=>v.1.2) t; cases congrArg Prod.snd t; rfl }
variable (h:Hosp S N)
local notation "J"=> occupy S N h
local notation "φ"=> star (flake (Tset N)ᶜ)

private lemma stone_age (i:Tag S):∃ a:ℂ, ‖a‖ =1 ∧ twist φ ((velvet S N).term i)= a • put (J i):=by
 obtain ⟨⟨x,g,t⟩,p⟩:=i; let v:Tag S:=⟨(x,g,t),p⟩
 change ∃ a:ℂ, ‖a‖ = _∧twist φ (thread N (x,g,t))=_
 let q:= Lifted.index N x g t; have hv:J v=q:=rfl
 let k:=Lifted.winding N x
 unfold thread basisC; dsimp only; rw [map_smul]; split
 · next ht=>
    refine ⟨k,(Rush.fee_norm _),?_ ⟩; rw [create_put, twist_scalar,←show drift (Tset N)ᶜ q=put q from if_neg fun h=> (mem_compl.mp h) ((mem_Tset ..).2 ht), flake_flip_p]; rfl
 next u=>
 refine ⟨star k,(by rw [norm_star]; exact Rush.fee_norm _),?_⟩
 unfold Fock.remove; rw [map_smul,star_smul,create_put, twist_scalar]; change star k • twist φ (takeF q)=star k • put q; rw [ ←show drift (Tset N)ᶜ q=takeF q from if_pos (mem_compl.mpr fun h=>u ((mem_Tset ..).1 h)), flake_flip_p] -- star(put)=takeF def

lemma museum (s:Finset (Tag S)):∃ a:ℂ, ‖a‖=1 ∧ twist φ ((velvet S N).tag s)=a • poke (s.map J):=by
 induction s using Finset.induction_on with
 | empty=> exact ⟨1,norm_one,by rw [Finset.map_empty,Poly.tag_void,map_one, one_smul,poke,Poly.tag_void]⟩
 | insert i s p ih=>
    obtain ⟨a,v,e⟩:= ih; let q':=(velvet S N); obtain ⟨b,t,f⟩:=stone_age S N h i
    have ht:J i∉s.map J:= fun v=> (by obtain ⟨j,u,e⟩:=Finset.mem_map.mp v; exact p (((J).injective e) ▸ u))
    let c:=Fock.parity i s; let d:= Fock.parity (J i) (s.map J)
    refine ⟨c*a*b*d,by simp [norm_mul,d,c,Fock.parity,v,t],?_⟩
    rw [Poly.tag_any _ s i p,twist_scalar,map_mul,e,f, Finset.map_insert, show poke (insert (J i) (s.map J))= _ from Poly.tag_any (cane _) _ _ ht]
    simp only [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul]
    change _ • (put _ * _)= (c*a*b*d*d) • _ -- assoc
    rw [mul_assoc (_*_*b),parity_sq,mul_one]; exact congrArg (fun (a:ℂ)=> a • (put (J i) * poke (s.map J))) (mul_assoc c a b).symm

-- host supplies field extension since agreement matters only on endpoints; if injecting on S that's enough (no need step tips, can extend by edge tail here!).
include h
lemma tail (V:LinksC)(i:Edge Cover)(t:i.1∈ S):onC N (graft S N V) i= V i:=by
 rcases i with ⟨a,k⟩
 let q:↥S:=⟨a,t⟩
 have p:∃ b:S,pole S N b= (wrap (More N) a):=⟨q,rfl⟩
 rw [onC_spec]; unfold graft; dsimp only; rw [dif_pos p]
 let x:= Classical.choose p; have ht:x.val=a:=h.seat_ x.property t (Classical.choose_spec p)
 change V (x.val,k)=_; rw [ht]

omit h
variable (K: Calibration)(F:Family K){m:Side}
-- given evaluation at m, can read all coefficients by crumbs uniformly across even sets. Works at ANY such m.
lemma ruby (a:Evens S→Purse S)(t:F=∑ x:Evens S,note K (a x).val (tagWord S x.val))(p:Hosp S (K.c m))(y:ℝ)(hy:∀ x, ‖F m x‖ ≤ y): ∀ t:Evens S,∀ x:PairsC, ‖(a t).val x‖ ≤ y:=by
 let n:=K.c m; let φ0:=star (flake (Tset n)ᶜ); let J0:= occupy S n p
 intro i r
 choose u hu v using museum S n p
 let D:= replant S n r; let R(x:PairsC):=Prod.map (onC n) (onC n) (replant S n x)
 have hr(x:Evens S): (a x).val (R r)=(a x).val r:= by apply (a x).property.locus <;> exact fun i has _=>tail S n p _ _ has
 have he: twist (star (flake (Tset n)ᶜ)) (F m D)=∑ i:Evens S, (a i).val r • (u i.val • poke (i.val.map J0)) := by
    rw [t]; simp_rw [Finset.sum_apply,map_sum,note_v,spool_sing,velvetTag,twist_scalar]; apply sum_congr rfl; intro x _; change (a x).val (R r) • (twist (star (flake (Tset n)ᶜ))) ((velvet S n).tag _)=_; rw [v,hr]
 let T:= i.val.map J0
 have hp:crumb (twist φ0 (F m D)) T=((a i).val r)*(u i.val):=by
    rw [he, crumb_sum,sum_eq_single i, crumb_scale,crumb_scale,Pastry.chip,if_pos rfl,mul_one]
    · intro j _ K; rw [crumb_scale,crumb_scale,Pastry.chip,if_neg ?_,mul_zero,mul_zero]; exact fun x=> K (Subtype.ext (Finset.map_injective J0 x.symm))
    simp
 have hz:=calc
    ‖crumb (twist φ0 (F m D)) T‖ ≤ ‖twist φ0 (F m D)‖ := norm_entry _ _ _
    _ ≤ y:= by rw [twist_norm]; exact hy D
 rwa [hp,norm_mul,hu,mul_one] at hz
