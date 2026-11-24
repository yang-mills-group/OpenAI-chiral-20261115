import YM.CF.Cascade.Eel
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m X B L:Side}{ho:Odd L.val}{d e:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{P:Grasp Y B e} {G:Ratio (CSide m B) (CSide X B)}{T:Roam m X B}{F:Forest T.ratio}{z:Vox m B→AxisChart group F}{M: Male}
open Pec
local notation "dη"=>Aroma.port
local notation "μN"=> Ember.pinch
structure Interest (n:Side) where
 M:Male
 P:Aim n
 I:Pride n
namespace Interest
variable {N:Side}(P:Interest N)
def spent(u:CoreX)(j:ℕ):= bookie N u P.P P.M j P.I (dη N)/base_u N
def under (a b c d e f:ℝ):Prop:= P.P.toll a c b d ∧ Lac P.I e f
end Interest
structure Valued (j:ℕ)(L:Side)(ho:Odd L.val)(a b d e:ℝ)(t:ℕ)(m A B:Side) (Y:Pricing j L ho (Vault.Thread j))(P:Grasp Y B e) (p q:ℕ) (k B' C x y:ℝ) (I:Interest (CSide m B))(J: Interest (CSide A B))(α:ℝ):Prop where
 path:∃ (G:Ratio (CSide m B) (CSide A B))(T:Roam m A B)(F:Forest T.ratio)(z:Vox m B→ AxisChart group F)(H:Hull j L ho a b d e t m A B G T F z Y P)(W:RG.PathData group)(r:RG.Clip)(σ η D:ℝ)(A':Bed)(l:Flight p q)(h:l.L=L)(p': (More (CSide A B)).val = (More (CSide m B)).val*l.L.val), W.Bounds r σ η D∧ Attached A' W∧ (∃ Wm D':ℝ, Floor A' r (More (CSide m B)) Wm D') ∧ A'.metric.strip B' C ∧ Bid.Sworn A' (More (CSide m B)) group ∧ I.M=upMale L ho J.M ∧ Guessed F (installed (l.visitRatio p') (l.duo k).A0) z ∧ Horizon F z 2 x y∧ TimeC J.M J.P I.P J.I I.I H r W α
-- arithmetic cumulative corrections. One schedule later fills every step.
structure Desc (j:ℕ)(L:Side)(ho:Odd L.val)(a b d e:ℝ)(t:ℕ)(B:Side) (Y:Pricing j L ho (Vault.Thread j))(P:Grasp Y B e) (p q:ℕ) (k B' C x y:ℝ) (N:ℕ→Side) (I:∀ i,Interest (CSide (N i) B))(α: ℕ→ℝ)(v:ℕ):Prop where
 follow(i:ℕ)(h:i<v):Valued j L ho a b d e t (N i) (N (i+1)) B Y P p q k B' C x y (I i) (I (i+1)) (α i)
section money
variable {C a:ℝ}
lemma growT (n f:Side)(G: Ratio n f): Taper f=Taper n*Taper G.count:=by unfold Taper Natht; rw [G.exact_size,Nat.cast_mul]; exact Real.sqrt_mul (by positivity) _
lemma localG(F:ℕ→Side)(P A:ℕ→ℝ)(l C B:ℝ)(L:Side)
    (hh:0≤B)(t:4≤L.val)(k:ℕ)(h: ∀ i, i<k → ∃ g:Ratio (F i) (F (i+1)),g.count=L)(e:∀ i, i≤k → |P i-l*Real.log (F i).val|≤ C)
    (y:∀ i, i<k → |P i+A i-P (i+1)|≤ B/Taper (F i)) :
    |(∑ i∈range k,A i)-k*(l*Real.log L.val)|≤2*B+C+C:=by
 let d(i):=P i+A i-P (i+1)
 have hx(i)(g:i<k): B/Taper (F i)≤ 2*B*( (Taper (F i))⁻¹ - (Taper (F (i+1)))⁻¹):=by
    obtain ⟨G,p⟩:= h i g; rw [growT _ _ G,p]; obtain ⟨r,v,w,-,-⟩:=pineN L; have he : 2 ≤ Taper L:=by nlinarith only [r,w,(show 4≤Natht L by exact_mod_cast t)]; done
    let u:= Taper (F i); have hu:= pineN (F i); have hy:0<u:=hu.1; change _≤ 2*B*(u⁻¹- (u*Taper L)⁻¹); have ht:(u*Taper L)⁻¹ ≤ (u*2)⁻¹:= inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left he hy.le); apply le_trans (le_of_eq (show B/u= 2*B*(u⁻¹ - (u*2)⁻¹) by field_simp; ring)); gcongr
 have ht (n:ℕ)(g:n≤k):|(∑ i∈range n,d i)|≤2*B*( (Taper (F 0))⁻¹-(Taper (F n))⁻¹):=by
    induction n with
    | zero=>simp
    | succ n ih=> rw [sum_range_succ]; refine (abs_add_le ..).trans ((add_le_add (ih (by omega)) ((y n (by omega)).trans (hx _ (by omega)))).trans_eq (by ring))
 have hy(n:ℕ)(g:n≤k): (∑ i∈ range n,d i)=P 0+(∑ i∈range n,A i)-P n∧Real.log (F n).val = Real.log (F 0).val +n*Real.log L.val:=by
   induction n with
   | zero=> simp
   | succ n ih=> obtain ⟨ht,hx⟩:= ih (by omega); obtain ⟨G,p⟩:= h n (by omega); rw [log_l G,p,hx]; rw [sum_range_succ,sum_range_succ,ht]; refine ⟨?_,?_⟩; unfold d; abel; push_cast; ring
 obtain ⟨hp,h⟩:= hy k le_rfl; have hu:|(∑ i∈range k,d i)|≤2*B:= by
    apply (ht k le_rfl).trans; apply mul_le_of_le_one_right (by positivity); exact (sub_le_self _ (inv_nonneg.mpr (pineN (F k)).1.le)).trans (inv_le_one_of_one_le₀ (pineN (F 0)).2.1)
 rw [show (∑ i∈ range k,A i)- k*(l*Real.log L.val)=(∑ i∈range k,d i)-(P 0-l*Real.log (F 0).val)+(P k-l*Real.log (F k).val) by rw [hp,h]; push_cast; ring]; exact (abs_add_le ..).trans (add_le_add ((abs_sub _ _).trans (add_le_add hu (e _ (Nat.zero_le _)))) (e _ le_rfl))
end money
theorem plateau (K:Pearl P)(h:Stamped j L ho Y)(p:0<e)(g:1≤j)(q:4≤L.val)(w:Spack j L ho a b d t)(u:0<a)(v:0<b)(s m:ℕ)(M:ℝ)(r:4≤s)(f:4≤m)(c:0<M)(K1 K2 K3 K4 x y X A β V Λ:ℝ)(h1:0<K1)(h2:0<K2)(h3:0<K3)(h4:0<K4)(ha:0<x)(hb:0<y)(hX:0<X)(hA:0<A)(hu:0<β)(hV:0<V)(hL:0<Λ):∃ i:ℕ,∃ C:ℝ,0<C∧∀ (N:ℕ→Side)(I:∀ i,Interest (CSide (N i) B))(U:ℕ→ ℝ)(k:ℕ), (∀ i, i≤k →(I i).under K1 K2 K3 K4 x y) → (∀ j, j≤k → i≤(CSide (N j) B).val ∧ Even (CSide (N j) B).val)→(∀ i, i<k → |U i|≤ Λ)→ Desc j L ho a b d e t B Y P s m M X A β V N I U k→ |(∑ i∈range k,U i)-k*(spiceM*Real.log L.val)|≤C:=by
 haveI : Nontrivial CoreX:= yet_one.nontrivial_color; obtain ⟨z,hz⟩:= exists_norm_eq CoreX zero_le_one; obtain ⟨i,C,hc,T⟩:=math_p j g z hz K1 K2 K3 K4 x y h1 h2 h3 h4 ha hb
 obtain ⟨k,H,hH,J⟩:= equalH r f c L Λ C X A hL hc hX hA; obtain ⟨t',F⟩:= hol_proj j g; refine ⟨i+k+P.roundZ+t'+4, _, (show 0<2*H+C+C by positivity),fun N I U n ht hh hl hd=>?_⟩
 let D i:=CSide (N i) B; let t(i):= (I i).spent z j
 have he(i)(v:i≤n): Aurora (bookie (D i) z (I i).P (I i).M j (I i).I) (D i) C:=by
    obtain ⟨u',a⟩:=ht i v; obtain ⟨e,y⟩:=hh i v; have hQ:=T h p (by omega : P.roundZ≤(CSide (N i) B).val) (by omega) (I i).P (I i).M (I i).I u' a y; exact ⟨hQ.1,hQ.2⟩ -- binder missing I
 apply localG D t U spiceM C H L hH.le q n (fun i x=> ?_) (fun i p=> (he i p).hint) (fun i p=> ?_)
 · obtain ⟨G,T,F,z,H,-⟩:= (hd.follow i x).path; exact ⟨G,H.fromL⟩
 obtain ⟨G,T',Z,o,Y',W,r',μ,σ,tau,H',φ,qf,wp,Bp,hC,⟨ε,ν,χ⟩,hA',S,R,HR,Pv,Ho⟩:= (hd.follow i p).path -- tune tail Floor Exists
 let a:= (I (i+1)); let B':= I i; have hbI:= he (i+1) (by omega); obtain ⟨hx,hy⟩:=ht i p.le; obtain ⟨hv,hK⟩:=ht (i+1) (by omega); have he:= (hh i p.le).1; have hp:= (hh (i+1) (by omega)).1
 have hm:= paying Y' a.M a.P B'.P a.I B'.I z hz (den_r hv) (den_r hx) hK.lead Ho H' Bp χ hC S (Row.rights _ _ hA' hX.le) (by unfold card_c; change 3 ≤ (CSide (N i) B).val * 2; omega) r f wp c HR (F _ (by omega) _) (F _ (by omega) _) (pos_l Y' a.M a.P hv K u v h1 h3 h2 h4 Pv hu hV)
 have hx:B'.M= upMale L ho a.M:= R; rw [← hx] at hm; exact J φ qf _ _ G Y'.fromL _ _ _ H' (by omega) hA' χ.starts hbI (hl _ p) hm
end YM.CF.Cascade
