import YM.CF.Hest.Gust
import YM.CF.Hest.Foy
import YM.CF.Hest.Hull
import YM.CF.Facet.Prima
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 25000
noncomputable section
namespace YM.CF.Hest
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory Urn Levier Cour Facet
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N P m X B L:Side}{n k j:ℕ}{e d t x u C A:ℝ}
variable {G:Ratio (CSide m B) (CSide X B)}
variable (L)
abbrev cropL (L:Side)(o:Odd L.val)(j:ℕ)(K:WG ι)(M:ι→Male): Script ι:=fun i _ _ G x=> capT (wh j L o true (M i) G x) (endorse G (K i _ x.2))
lemma hP (L:Side)(o:Odd L.val)(K:WG ι)(H:Lively K)(J:ι→Male)(h:Even j)(p:1≤j):Save L false false (cropL L o j K J):=by
 let V:= transportS (Peaks.cup j L o h p (canUse j L o) true |>.2.2) J; exact (((Save.one ι).sub V).mul (hailing L o K H)).mul V
abbrev Budget(h:Odd L.val)(f:Dress (CSide X B))(v:Dress (CSide m B))(G:Ratio (CSide m B) (CSide X B))(M:Male)(j:ℕ)(i:nomA m X B): Op (Single (CSide m B)):= era L j h G M i (f i.1)-partM L j h m B M v i.2
variable {p s b a c r:ℝ}
-- quote Φ matching kernels. supply.
lemma central(j:ℕ)(h:Odd L.val)(U:Dress (CSide m B))(u: Nom (CSide m B) (CSide X B))(M:Male)(G:Ratio (CSide m B) (CSide X B)): partM L j h m B M U u.2=summit (patchQ G) (capT (wh j L h true M G (unionP u)) (endorse G (U u.2))):=by
 let S:=wh j L h true M G (unionP u); let P:=spar j (upMale L h M) u.2
 have he:S=lobe G true*(1-hood G)+ endorse G P:=rfl
 apply Thera.endorseI G; let T:= hood G; let V:= U u.2; let K:=endorse G V; have ht (V): T* endorse G V= endorse G V:=by unfold T hood; rw [rude,one_mul]
 have hu (V): endorse G V*T=endorse G V:=by unfold T hood; rw [rude,mul_one]
 have hx:T*T=T:=(hood_proj G).1; have hv:T*(lobe G true)=lobe G true*T:= (spurH ..).eq.symm
 have hl:S*T=endorse G P:=by rw [he, add_mul,mul_assoc, show (1-T)*T=0 by rw [sub_mul,hx,one_mul, sub_self],mul_zero,zero_add,hu]
 have hy:T*S=endorse G P:=by rw [he,mul_add,←mul_assoc,hv,mul_assoc,show T*(1-T)=0 from ?_,mul_zero,ht,zero_add]; rw [mul_sub,hx,mul_one,sub_self]
 rw [spry]; change endorse G ((1-P)*V*P)=T*((1-S)*K*S)*T; rw [←mul_assoc T,←mul_assoc T (1-S),mul_sub,mul_one,hy, sub_mul T,show T*K=K from ht _,mul_assoc _ S,hl]; unfold K; rw [rude, show endorse G V-endorse G (P*V)=endorse G (V-P*V) from ?_,rude,sub_mul (1:Op _) P V,one_mul]; ext i j; by_cases h:en G i ∧ en G j<;>simp [endorse,extendK,h]
variable {w:Odd L.val}{Y:Pricing j L w (Thread j)}{P': Grasp Y B e}
lemma prism_h(T:Aim (CSide X B))(V:Aim (CSide m B))(F:Tulip.Male) (M:Pearl P')(g:Stamped j L w Y)(hG:G.count=L)(hv:P'.roundZ≤ (CSide m B).val)(h:0<e)(j':1≤j)(ha:Ample T.den)(ht:Ample V.den)(he:Reef.Cry T)(hk:Reef.Cry V)(iK:nomA m X B)(p: Hops G j w T F iK)(u:iK∈ Rent0 G e)(k:Sweep (CSide m B)): Budget L w T.den V.den G F j (stanza G (castX k) (xtra k.charge) iK)=yank k.charge (castX k) (spinU k.charge k.s) (Budget L w T.den V.den G F j iK):=by
 let v:=iK; let S:=Shape.broad G (castX k); let W:= stanza G (castX k) (xtra k.charge) iK; let γ:=spinU k.charge k.s; let X:=yank (N:=CSide m B) k.charge (castX k) γ
 have hO:= (coast F M g hG k.charge (castX k) v u ha.self.1 j' ha he hv h p).2; have hl:partM L j w m B F V.den W.2= X (partM L j w m B F V.den v.2):=by
    let M':= upMale L w F; let B':=spar j M' W.2; let E:= prepU (castX k) γ (xtra k.charge) (CSide m B) -- shadow
    let hB:= P'.broadness _ hv M'; have hw:W∈ Rent0 G e:=alongS _ _ _ _ _ u; have hy:=hB.projection _ (JointB.cg hw); have hp:= peak_f V ht hk (castX k) k.charge γ (spinZ ..) v.2; -- tune use funde_f from Laic
    have h:sings k.charge E (spar j M' v.2)=swapX (detX k.s) B':=funde_f _ _ _ (spinZ ..) _ _ j' _ _ (g.fields_one _ (P'.needed.trans hv)) ((JointB.cg u).shrink P'.gem)
    unfold partM; rw [show V.den W.2=X (V.den v.2) from hp]; exact Levier.prima E _ _ _ hy h
 have ht(x y): X (x-y)=X x-X y:=by unfold X yank Thera.jazz turnsH; split<;> rw [singT,win_l,map_sub] <;> first|rfl|(rw [←singT,←singT,star_sub]; abel)
 unfold Budget; rw [show stanza _ _ _ _=W from rfl,show era L j w G F W (T.den W.1)= _ from hO,hl]; exact (ht ..).symm
end YM.CF.Hest
