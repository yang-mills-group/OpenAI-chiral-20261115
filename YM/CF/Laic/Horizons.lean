import YM.CF.Laic.Inch
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m A B L:Side}{j k:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
variable {e:ℝ}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{Y:Pricing j L ho (Thread j)}{V:Grasp Y B e}
-- Lever budget assembly
structure LawT (j k:ℕ) (β C D E:ℝ) :Prop where
 booth (L:Side) : 4≤L.val → ∀ l r:ℝ,0<l → l≤β → 0≤r→ ∃ W:ℕ,∀ {m N K: Side}{G:Ratio (CSide m K) (CSide N K)}{T: Roam m N K}{F:Forest T.ratio}{z:Vox m K→ AxisChart group F}{ho:Odd L.val}{n:ℕ}{a b d e:ℝ}{Y:Pricing j L ho (Thread j)}{V:Grasp Y K e}, Hull j L ho a b d e n m N K G T F z Y V→ Gazes T F z D r E→ W≤(More (CSide m K)).val→ ∀ M:Male,∀ A:ℝ,0≤A→∀ J:Toy k (CSide N K), CardK (CSide N K) k J A l→∀ u:Dress (CSide N K), relic u→ ∃ Q:Toy k (CSide m K),CardK (CSide m K) k Q (A*C/(L.val:ℝ)) l ∧ Nacre.crystal k (emergence L j ho G F z M (u+colorX J) -emergence L j ho G F z M u) (spurTx Q)
lemma paidW(h:1≤k)(w:k≤2)(p:Even j)(v:2≤j)(g:0<a)(hx:0<b):∃ u C:ℝ, 0<u∧ 0<C ∧ LawT j k u C a b:=by
 obtain ⟨z,H,s,f,R⟩:= natal h w p v a b g hx; refine ⟨z,H,s,f,⟨fun L e l k v p t=> ?_⟩⟩
 obtain ⟨W,D⟩:= R _ e l k v p t; refine ⟨W,fun {m N K G T F z ho n a b d e Y V} H h p M A w J q U l=>?_⟩; obtain ⟨y,h1,h2,q,k⟩:=D H h p M A w J q.1 q.2.1 q.2.2 U l; exact ⟨y,⟨h1,h2,k⟩,q⟩
abbrev matchedR (L:Side)(j:ℕ)(h:Odd L.val)(G:Ratio (CSide m B) (CSide A B))(F:Forest T.ratio)(z:Vox m B→AxisChart group F)(M:Male)(U:Dress (CSide A B))(u:Dress (CSide m B))(k:ℕ):Prop:= Nacre.crystal k (emergence L j h G F z M U-flareP L j h M u) 0
lemma matchedH (H:Hull j L ho a b d e n m A B G T F z Y V){U:Dress (CSide A B)}{u:Dress (CSide m B)}{M:Male}(h:relic U)(v:relic u)(Q:matchedR L j ho G F z M U u k):cFoot (k+1) (emergence L j ho G F z M U-flareP L j ho M u):=by
 have hp:= (H.terms M h).2.2.2
 -- need smooth spar. derive from W tape
 have hc: ContDiffAt ℝ ω (fun x:Vox m B=> spar j (upMale L ho M) (represent x)) 0:=by
    let V:=wh j L ho true M G
    have he:legal G d∈𝓝 (unionP (ears F z 0)):= (Peaks.cabin ..).mem_nhds (ambient _ _ H.po le_rfl (H.native.melod d H.po G).self_of_nhds)
    have hh:ContDiffAt ℝ ω (fun i=>V (unionP (ears F z i))) 0:= (crown_air G (H.tape.U M G H.fromL H.request) _ he).comp (f:=unionP ∘ ears F z) _ H.native.tarnish
    let f(i:Vox m B):= spar j (upMale L ho M) (represent i); have hz(i): f i=summit (patchQ G) (V (unionP (ears F z i))-lobe G true*(1-hood G)):=by
       rw [show V _= _ from (show V _=lobe G true*(1-hood G)+ endorse G (f i) from rfl),add_sub_cancel_left]; rw [←edgeDesk]; ext x y; exact (desk_at (patchQ G) (f i) x y).symm
    change ContDiffAt ℝ ω f 0; rw [funext hz]; refine Nacre.tort.mpr fun i j=>?_ ; exact Nacre.tort.mp (hh.sub (g:=fun _=> lobe G true*(1-hood G)) contDiffAt_const) _ _
 exact nextF ((hp.sub ((ContDiffAt.mul ((contDiffAt_const.sub hc).mul v.2) hc): ContDiffAt ℝ ω (flareP L j ho M u) 0)).of_le le_top) Q -- parentheses
lemma synergy (H:Hull j L ho a b d e n m A B G T F z Y V)(M:Male){U:Dress (CSide A B)}{u:Dress (CSide m B)}(p:relic U)(v:0<k){A':ℝ}{x:Toy k (CSide m B)}{l:ℝ}(hc:CardK (CSide m B) k x A' l)(X:Nacre.crystal k (emergence L j ho G F z M U-flareP L j ho M u) (spurTx x)) {J:Toy k (CSide A B)}{y: Toy k (CSide m B)}{w C:ℝ}(K:CardK (CSide A B) k J w l)(Y: CardK (CSide m B) k y C l)(V:Nacre.crystal k (emergence L j ho G F z M (U+colorX J)-emergence L j ho G F z M U) (spurTx y)) : matchedR L j ho G F z M (U+colorX J) (u+colorX (x+y)) k:=by
 have ht: Nacre.crystal k (emergence L j ho G F z M (U+colorX J)-flareP L j ho M u) (spurTx (x+y)):=by
   rw [(carK x y hc.1 Y.1 hc.2.1 Y.2.1).2.2.2]; intro i; refine ((X i).add (V i)).congr (fun j=>?_); change _ + _= _; simp only [← smul_add,Pi.sub_apply]; congr 1; abel
 exact mender H M (relic_up p (relic_r k v J).2.1) (x+y) ht
lemma atZero (F:Forest T.ratio)(G:Ratio (CSide m B) (CSide A B))(v:0<a):reqU G F 0 a 1 k∧ reqQ G F 0 a 1 k:=by
 have ht: (fun i:Snap F=> endorse G (0:Op (Single (CSide m B))))=fun _=>0:= funext fun _=> betP (0:Op (Iota G)); unfold reqQ; simp only [Pi.zero_apply,ht]; exact ⟨HoldX.cold v, HoldX.cold v⟩
end YM.CF.Laic
