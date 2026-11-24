import YM.CF.Hom.Clare
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Hom
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker
variable {L B A m:Side}{ho:Odd L.val}{j k:ℕ}{a b d r s u v n X l η e:ℝ}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}
variable {G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F D:Forest T.ratio}{z:Vox m B→ AxisChart group F}{h: Vox m B→ AxisChart group D}
variable {R19 R:RG.PathData group}{q:RG.Clip}
section leg
open scoped Matrix.Norms.Frobenius
lemma pay_f (w:R.Bounds q n X l)(p:T.patch.Branches T.kernel group)(t:Critical F q R z)(r:Critical D q R h)(e:PriceGap D q R η)(g:0<η)(W:Nativity F z):∀ᶠ i in 𝓝 0,∃ k:Site (More (CSide A B))→SU.E,k ∘ T.ratio.embed=1∧ baby D h i=Lattice.gauge k (baby F z i):=by
 let U:=Stationary.arm group (More (CSide m B)) 1; let V:=(natJoint F z); let I:T.Choices:= Classical.arbitrary _; have hd:Tendsto U.symm (𝓝 0) (𝓝 0):=by simpa using U.symm.continuous.tendsto 0
 have he := Stationary.veterans r p w e g I W.army W.flat' U.symm.contDiff.contDiffAt (map_zero U.symm) (hd.eventually (Stationary.camp_station t p w I)) -- tune
 filter_upwards [he] with i hi; let z:= Stationary.boots T D (V i); refine ⟨z,?_,(congrArg Prod.fst hi).symm⟩; funext j; have hv := congrFun (congrArg Prod.snd hi) j; change (z (T.ratio.embed j))=1; change 1 * (1:SU.E) * (z (T.ratio.embed j))⁻¹=1 at hv; simpa using hv
end leg
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma ActZ_one(N:Side)(x: Op (Single N)):ActZ 1 x=x:=by unfold ActZ tradew; simp only [Pi.one_apply,map_one, twist_formula]; rw [show jump (Equiv.refl (Site N × SpinIdx)) (fun _=>(1:UNI SU.Slot).val)= (1:Op (Single N)) from jump_id,one_mul,star_one,mul_one]
lemma moveP (H: Hull j L ho a b d e k m A B G T F z Y P)(Q:Pearl P)(M:Male)(x: Aim (CSide A B))(y:Aim (CSide m B))(u:Pride (CSide A B))(V:Pride (CSide m B))(q':RG.Clip)(g:ℝ)(hx:Ample x.den)
 (p: cFoot 3 (emergence L j ho G F z M x.den -flareP L j ho M y.den)) (t:cFoot 3 (myth G F z q' R19 P M x.den u V g)) (hs:R.Bounds q n X l)(hs':T.patch.Branches T.kernel group)(hy:Critical F q R z)(w:Critical D q R h)(v:PriceGap D q R η)(hd:0<η): cFoot 3 (emergence L j ho G D h M x.den-flareP L j ho M y.den) ∧ cFoot 3 (myth G D h q' R19 P M x.den u V g):=by
 have he:∀ᶠ i in 𝓝 0, pigment u (baby D h i)=pigment u (baby F z i)∧emergence L j ho G F z M x.den i=emergence L j ho G D h M x.den i∧ lush G P M x.den (ears F z i)= lush G P M x.den (ears D h i):=by
    filter_upwards [pay_f hs hs' hy w v hd H.native, H.native.melod e H.hi G,H.native.melod d H.po G,H.nickP M hx.self] with i hG he ht hh; obtain ⟨g,k,p⟩:=hG; let Z:= ears F z i; let X:= x.den (baby F z i)
    have hr:scaleG G g=1:=by unfold scaleG; rw [←H.alignT]; exact k
    have hl: ears D h i=july G g Z:=Prod.ext p (by change represent i=Lattice.gauge (scaleG G g) _; rw [hr,Stationary.gauge_one]; rfl)
    obtain ⟨b,c⟩:= Dusk H.tape G M H.fromL H.request Z (ambient _ _ H.po le_rfl ht) g X hh.1; rw [hr, ActZ_one] at b; refine ⟨p ▸ pinG ..,?_,?_⟩
    · unfold emergence; rw [p,hx.ripe,hl]; exact b.symm
    unfold lush; rw [hl,fame H M Q Z he]; change _= _- invoice (gate _ _ _ _ _ _ (x.den (gauge g _))); rw [hx.ripe]; change _= -(altar G P Z M) - invoice (gate _ _ _ _ _ _ (ActZ g X)); rw [show gate L j ho G M _ _=twist _ (gate L j ho G M Z X) from c,bill_invariant _ (gate L j ho G M Z X) hh.1]; rfl
 have hp : emergence L j ho G D h M x.den-flareP L j ho M y.den=ᶠ[𝓝 0] emergence L j ho G F z M x.den-flareP L j ho M y.den:=he.mono fun i h=> congrArg (· - _) h.2.1.symm
 have hv: myth G D h q' R19 P M x.den u V g =ᶠ[𝓝 0] myth G F z q' R19 P M x.den u V g:= he.mono fun i v=> by simp only [myth,deflate,Function.comp_apply]; rw [v.1,← v.2.2,← he.self_of_nhds.2.2]
 exact ⟨fun i h=>(hp.iteratedFDeriv ℝ i).eq_of_nhds.trans (p i h),fun i h=>(hv.iteratedFDeriv ℝ i).eq_of_nhds.trans (t i h)⟩
end YM.CF.Hom
