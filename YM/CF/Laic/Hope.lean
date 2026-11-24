import YM.CF.Laic.Horizons
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m A B L:Side}{j k:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
structure Aim (S:Side) where
 x:Toy 1 S
 y:Toy 2 S
namespace Aim
variable {G:Side}
def toll(W:Aim G)(x y a b:ℝ):Prop:=CardK G 1 W.x a x ∧ CardK G 2 W.y b y
def den(W:Aim G):Dress G:= colorX W.x+colorX W.y
end Aim
variable {r s u v w y β α:ℝ}
lemma limits (L:Side)(g:2*y ≤ L.val)(p:0<v): v+ 2*v*y/(L.val:ℝ)≤2*v:=by
 have he:0<(L.val:ℝ):= by exact_mod_cast L.property
 have hp:2*v*y/L.val≤ v:=by apply (div_le_iff₀ he).mpr; nlinarith
 linarith
variable {e:ℝ}{G:Ratio (CSide m B) (CSide A B)}{T: Roam m A B}{F:Forest T.ratio}{z: Vox m B→ AxisChart group F}
lemma capH {w:ℕ}(p:Horizon F z k a b)(v:w≤k): Horizon F z w a b:=⟨p.smooth,p.flat,fun i hi h=> p.p _ hi (h.trans v)⟩
structure Magic(j:ℕ)(α β:ℝ)(N:Side)(ho:Odd N.val)(Y Z σ a b d:ℝ)(r:ℕ)(i x k y:ℝ)(n:ℕ):Prop where
 give {m C B:Side}{G:Ratio (CSide m B) (CSide C B)} {T:Roam m C B}{F:Forest T.ratio}{z:Vox m B→AxisChart group F}{e:ℝ}{P:Pricing j N ho (Thread j)}{V:Grasp P B e}(H:Hull j N ho a b d e r m C B G T F z P V)(g:Gazes T F z α σ β)(h:Horizon F z 2 Y Z)(l:n≤(More (CSide m B)).val)(M:Male)(W:Aim (CSide C B))(f:W.toll x y i k) :∃ K:Aim (CSide m B), K.toll x y i k ∧ cFoot 3 (emergence N j ho G F z M W.den - flareP N j ho M K.den)
lemma travelW(k:ℕ)(g:2≤k)(p:Even k)(t:0<α)(q:0<β):∃ n:ℕ,∀ (L: Side),n≤L.val→∀ (h:Odd L.val) (r:ℕ) (Y Z σ a b d:ℝ),0<Y→0<Z→0≤ σ→0<a→0<b→0<d→Spack k L h a b d r→∃ i x K y:ℝ,0 < i ∧0<x∧0<K∧0<y∧∃ v:ℕ, Magic k α β L h Y Z σ a b d r i x K y v:=by
 obtain ⟨v,C,hc,hV,E⟩:= paidW (k:=1) (by norm_num) (by norm_num) p g t q; obtain ⟨s,D,hs,hD,Q⟩:= paidW (k:=2) (by norm_num) le_rfl p g t q
 obtain ⟨N,hN⟩:= exists_nat_gt (2*max C D)
 refine ⟨max 4 N,fun L he h r Y Z σ a b d hp hz hy ha hb hd P=>?_⟩; have hk : 4≤ L.val:=(le_max_left ..).trans he; have hf:2*max C D ≤ L.val:= hN.le.trans (by exact_mod_cast (le_max_right 4 N).trans he)
 obtain ⟨u,B,hU,hB,X⟩:= repairs (r:=1) (d':=1) (by norm_num) (by norm_num) hp hz P ha hb hd 1 -- tune
 let x:=min u v; have hx:0<x:=lt_min hU hc; obtain ⟨c,A,f,k',I⟩:=skyK x (2*B) L hx (by positivity) 1 2
 obtain ⟨w,K,hW,hK,W⟩:=repairs f k' hp hz P ha hb hd 2
 let y:=min w s; have ht:0<y:=lt_min hW hs; obtain ⟨R,M⟩:= E.booth L hk x σ hx (min_le_right ..) hy; obtain ⟨T,H⟩:=Q.booth L hk y σ ht (min_le_right ..) hy
 refine ⟨2*B,x,2*K,y,mul_pos (by norm_num) hB,hx,mul_pos (by norm_num) hK,ht,max R T,⟨?_⟩⟩
 intro m C' B' G T' F z e P' V hh u' p l M' U t; obtain ⟨T₁,T₂⟩:=t
 let Ux:= colorX U.x
 have he:cFoot 1 (emergence L k h G F z M' 0 - flareP (m:=m) (B:=B') L k h M' 0):=by
    intro i hi; rw [show i=0 from by omega]; rw [partZero]; ext; rw [iteratedFDeriv_zero_apply]; rw [Pi.sub_apply,hh.val M' relic_zero]; simp
 obtain ⟨b',X₁,hX⟩:= X hh (capH p (by norm_num)) M' 0 0 bare bare ((atZero F G (k:=1) zero_lt_one).1) ((atZero F G (k:=1) zero_lt_one).2) he
 obtain ⟨a',X₂,h₁⟩:= M hh u' ((le_max_left ..).trans l) M' _ (by positivity) U.x T₁ 0 relic_zero
 let p':=b'+a'; have hj:CardK _ _ p' (2*B) x:=qmon (car_c (qmon X₁ le_rfl (min_le_left u v)) X₂) (limits L (le_trans (mul_le_mul_of_nonneg_left (le_max_left ..) (by norm_num)) hf) hB) le_rfl
 have hQ: matchedR L k h G F z M' Ux (colorX p') 1:=by simpa only [zero_add] using synergy hh M' relic_zero (by omega) (qmon X₁ le_rfl (min_le_left u v)) hX T₁ X₂ h₁ -- width
 have hT:=amp_P _ (by norm_num) T₁.1 T₁.2.1; have hx':=amp_P _ (by norm_num) hj.1 hj.2.1; obtain ⟨f',V',hv⟩:= W hh p M' _ _ hT hx' ((I _ _ hh.alignT hh.fromL h).1 _ T₁.2.2) ((I _ _ hh.alignT hh.fromL h).2 _ hj.2.2) (matchedH hh hT.self hx'.self hQ)
 obtain ⟨g',Y',g⟩:= H hh u' ((le_max_right ..).trans l) M' _ (by positivity) U.y T₂ _ hT.self
 have hp:CardK _ _ f' K y:= qmon V' le_rfl (min_le_left w s); let q:= f'+g'; have hB': CardK _ _ q (2*K) y:= qmon (car_c hp Y') (limits L (le_trans (mul_le_mul_of_nonneg_left (le_max_right ..) (by norm_num)) hf) hK) le_rfl
 refine ⟨⟨p',q⟩,⟨hj,hB'⟩,?_⟩; have ht:= synergy hh M' hT.self (by omega) hp hv T₂ Y' g; exact matchedH hh (amp_plus hT (amp_P _ (by omega) T₂.1 T₂.2.1)).self (amp_plus hx' (amp_P _ (by omega) hB'.1 hB'.2.1)).self ht
end YM.CF.Laic
