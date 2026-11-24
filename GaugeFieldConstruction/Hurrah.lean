import GaugeFieldConstruction.Cranes
import YM.CF.Vale.Oak
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision RG Next.Free Work.F08 Craft Pressure Stationary Tree Reef Hom AnalyticBridge.LocalGaussianLaws
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius
open Exterior Next.Free.Stretch Finset Matrix
variable {n c f:Side}{K:Teller SU.group}{P:Patch}{R:ChartRatio SU.group}{W:Postal}(A:Gold K P R W)
abbrev GoldChain (i:ℕ)(n: Side):= Precision.K ((A.H i).metric.acts n)
variable (hK: K.top.clip.direct≤1)(hP:P.J=4)
include hK
lemma made_K : GoldChain A 0 n=(d 1 n)ᵀ * d 1 n:=by
 let q:=K.top.clip
 have he:= A.tied 0; rw [A.born] at he; let H:=A.H 0
 have he': Attached H (WilsonStartup.Design.top SU.group q):=⟨he.layout⟩ -- tune
 have hg:= WilsonStartup.Design.bed q
 have hk : H.roots = (WilsonStartup.Design.bed q).roots:=by
    funext i j x; obtain ⟨b,rfl⟩:= plaqEquiv.surjective i; obtain ⟨r,rfl⟩:=plaqEquiv.surjective j
    exact (he'.layout _ _ _).unique ((WilsonStartup.Design.attached q (G:=SU.group)).layout b r x) -- tune
 have hu: H.full q n=(WilsonStartup.Design.bed q).full q n:=by unfold Bed.full; rw [hk]
 unfold GoldChain Precision.K; rw [← ((A.roof 0).2.1 n).roots,show (A.H 0).full K.top.clip n=_ from hu, WilsonStartup.Design.full_root q hK n,Matrix.mul_one]
omit hK
lemma auric (j:ℕ)(x:f.val=c.val*P.L.val): ∃ Z:Matrix (Body 1 f) (Body 1 c) ℝ, Inputs (A.op j x) Z ((A.H j).metric.acts f) ((A.H (j+1)).metric.acts c):= ⟨_,((A.deed j).link (A.sized j x)).trial⟩
include hK hP
abbrev SpectBadge (j:form 1 c)(k:form 1 f)(L:Side):Prop:=∀ p:Momentum,Cycle f p→∀a, PriceM k p a=FilterT L p a * PriceM j (L.val •p) a
lemma summit_Q (o:ℕ) (g:Ratio c f)(e:g.count=P.L^o){x y j k:form 1 c}(vx: GoldChain A o c *ᵥ x=j)(vy: GoldChain A o c *ᵥ y=k)(z:Crossed j k): ∃ X Y J V:form 1 f,X ⬝ᵥ V=x ⬝ᵥ k ∧ ((d 1 f)ᵀ*d 1 f)*ᵥ X=J ∧ ((d 1 f)ᵀ*d 1 f)*ᵥ Y=V ∧ SpectBadge j J g.count ∧ SpectBadge k V g.count:=by
 induction o generalizing c with
 | zero=>
   simp at e; have hu:c=f:= by have he:=g.exact_size; rw [e] at he; simpa [eq_comm] using he -- tune
   subst c; rw [made_K A hK] at vx vy; refine ⟨x,y,j,k,rfl,vx,vy,?_,?_⟩ <;> simp [e,SpectBadge,FilterT,area]
 | succ o ih=>
   let b:=c*P.L; have hb:b.val=c.val*P.L.val:=rfl
   let G:Ratio b f:= ⟨P.L^o,by rw [g.exact_size,e,pow_succ',hb, PNat.mul_coe,mul_assoc]⟩
   let S:= A.op o hb; have hk:S.patch=P:=A.patch_x o hb
   obtain ⟨T,w⟩:=auric A o hb
   let I:= Tr S j; let I':=Tr S k; let u:= T *ᵥ x; let v:=T *ᵥ y
   obtain ⟨X,Y,J,V,m,U,u',q,q'⟩:= ih G rfl (execute S w vx) (execute S w vy) (pivotC S (congrArg Patch.J hk|>.trans hP) z) -- tune
   have E (j:form 1 c)(J:form 1 f)(q:SpectBadge (Tr S j) J G.count):SpectBadge j J g.count:=by
     intro p u₀ a; have hg:Odd G.count.val:=by dsimp only [G, PNat.pow_coe]; exact P.odd_side.pow
     have hx:Cycle b (G.count.val • p):= by intro x y h; rw [mode_scale,mode_scale]; apply u₀; rw [←G.embed_wrap,←G.embed_wrap,h]
     rw [q p u₀ a,(matadors S (congrArg Patch.J hk|>.trans hP) _ _ hx a), hk,e,pow_succ',show P.L ^o=G.count from rfl,← filter_mult P.L G.count P.odd_side hg p, PNat.mul_coe,mul_smul]; ring
   refine ⟨X,Y,J,V,?_,U,u',E j _ q,E k _ q'⟩
   have he:=funds S w vx k; rw [dotProduct_comm k j,past z,mul_zero,zero_add] at he; exact m.trans ((dotProduct_comm ..).trans (he.symm.trans (dotProduct_comm ..)))
-- invoice formula uses filter pM. can simplify cochain inputs p+stem p
open scoped ComplexOrder
omit hK hP in
lemma windyR (j:form 1 c) (p:Momentum)(l:Cover) : PriceM j (p+reciprocal l)=PriceM j p:=by
 ext1 a; unfold PriceM; congr 1; funext v; simp [perQ,mode_phase,mode_periodic]
abbrev BridgeT (p:Momentum)(b:Side)(J:TypeFace 1 → ℂ)(l:Site b)(a:TypeFace 1):= FilterT b (aliasAt p l) a*J a / (b.val:ℂ)
abbrev WaveT (j k:form 1 c)(L: Side)(p:Momentum)(l:Site L) := let T:= aliasAt p l; let B:=L.val • T; (divisor L B)⁻¹ * (BridgeT p L (PriceM k p) l ⬝ᵥ star (BridgeT p L (PriceM j p) l))
omit hK hP in
lemma risen (M:Side)(p:Momentum): divisor M (M.val • p)=(M.val:ℂ)^2*divisor 1 p:=by
 have he(x:Momentum):narrow M (M.val •x)=x:=by unfold narrow; rw [← Nat.cast_smul_eq_nsmul ℂ,inv_smul_smul₀ (side_ne M)]
 unfold divisor seedQ; simp_rw [← smul_neg,he]; simp [narrow,mul_sum]
 ring_nf -- sum tune
lemma east_K (o:ℕ)(g:Ratio c f)(e:g.count=P.L^o){x y j k:form 1 c}(vx: GoldChain A o c *ᵥ x=j)(vy: GoldChain A o c *ᵥ y=k)(z:Crossed j k): ((k ⬝ᵥ x:ℝ):ℂ)= (stageVolume c)⁻¹ * ∑ p:Site c, ∑ l:Site g.count, WaveT j k g.count (mon p) l:=by
 obtain ⟨X,Y,J,V,m,U,u,h,v⟩:= summit_Q A hK hP o g e vx vy z
 have hp:Odd g.count.val:= by rw [e, PNat.pow_coe]; exact P.odd_side.pow
 rw [dotProduct_comm k x,←m,dotProduct_comm X V,harvest_flux U u hp, ratio_volume g]; rw [mul_inv,mul_assoc]; congr 1
 rw [mul_sum]; refine sum_congr rfl fun p _=>?_ ; rw [mul_sum]; refine sum_congr rfl fun l _=>?_
 let t:= aliasAt (mon p) l; let L:=g.count; have hl: Cycle f t:=fun x y=>mesh_alias g p l -- tune
 have hf(a)(B:form 1 c)(C)(q:SpectBadge B C L): pack_R g C (p,l,a)=(L.val:ℂ) * BridgeT (mon p) L (PriceM B (mon p)) l a:=by
    rw [rhythm,q _ hl]; rw [show L.val • t= mon p+reciprocal (lift l) from alias_scale ..] -- tune reduc
    unfold BridgeT; rw [windyR, mul_div_cancel₀ _ (side_ne L)]
 unfold WaveT; dsimp only
 rw [dotProduct,dotProduct,mul_sum,mul_sum,mul_sum,risen]; refine sum_congr rfl (fun i _=>?_) -- goal i? nested
 simp only [Pi.star_apply, hf _ _ J h,hf _ _ V v,star_mul, star_natCast]
 unfold stageVolume L at *; field_simp [side_ne] -- tune
#print axioms east_K
end YM.CF.Vale
end
