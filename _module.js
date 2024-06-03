function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}
function null_to_empty(value) {
    return value == null ? '' : value;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function set_custom_element_data(node, prop, value) {
    if (prop in node) {
        node[prop] = typeof node[prop] === 'boolean' && value === '' ? true : value;
    }
    else {
        attr(node, prop, value);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link0;
	let link1;
	let link2;
	let link3;
	let script0;
	let script0_src_value;
	let script1;
	let script1_src_value;
	let link4;
	let link4_href_value;
	let meta2;
	let meta3;
	let meta4;
	let meta5;
	let meta6;
	let style;
	let t;

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link0 = element("link");
			link1 = element("link");
			link2 = element("link");
			link3 = element("link");
			script0 = element("script");
			script1 = element("script");
			link4 = element("link");
			meta2 = element("meta");
			meta3 = element("meta");
			meta4 = element("meta");
			meta5 = element("meta");
			meta6 = element("meta");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\n:root {\n  /* Fonts  */\n  --font-heading: 'Fraunces', serif;\n  --font-body: 'IBM Plex Mono', monospace;\n  --font-text: 'Work Sans', sans-serif;\n  \n  /* Colors */\n  --color-Y500: #E9D90A;\n  --color-Y400: #F6E500;\n  --color-Y300: #F7D254;\n  --color-Y200: #FFF587;\n  --color-Y100: #FFFCDA;\n\n  --color-P500: #E82884;\n  --color-P400: #FF4FA3;\n  --color-P300: #FF74B7;\n  --color-P200: #FFB1D7;\n  --color-P100: #FFD6E9;\n\n  --color-T500: #50ADBE;\n  --color-T400: #69C9DB;\n  --color-T300: #A8E1EC;\n  --color-T200: #C2F1FA;\n  --color-T100: #E2FAFF;\n\n  --color-G500: #C8C9DC;\n  --color-G400: #D5D7EF;\n  --color-G300: #E6E7FB;\n  --color-G200: #EEF2FD;\n  --color-G100: #F4F9FC;\n\n  --color-black: #000000;\n  --color-white: #FFFFFF;\n  \n  /* Base values */\n  --color-primary: var(--color-Y400);\n  --color-secondary: var(--color-P400);\n  --color-tertiary: var(--color-black);\n  --color-tertiary: var(--color-white);\n  \n  /* --color: var(--color-base);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #eee;\n  --background: white; */\n  --border: 0.851905px solid var(--color-black);\n  --border-radius: 4.25952px;\n  --max-content-width-mobile: 768px;\n  --max-content-width-small-desktop: 900px;\n  --max-content-width: 1200px;\n  --page-padding-desktop: 90px 80px;\n  --page-padding-small-desktop: 120px 60px;\n  --page-padding-mobile: 90px 18px;\n\n  --hero-padding-desktop: 150px 80px 90px 80px;\n  --hero-padding-large-desktop: 200px 80px 90px 80px;\n\n  --hero-padding-mobile: 100px 18px 90px 18px;\n  --content-padding: 0px 50px;\n  \n}\n\n\n#page a {\n    color: var(--color-black);\n  }\n\n\n#page h1,#page h2,#page h3,#page h4 {\n    font-family: var(--font-heading);\n    font-weight: 700;\n    color: var(--color-black);\n  }\n\n\n#page h1 {\n    font-size: 33px;\n    line-height: 39px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h1 {\n      font-size:  67px;\n      line-height: 69px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h1 {\n      font-size:  83px;\n      line-height: 93px\n  }\n    }\n\n\n#page h2 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h2 {\n      font-size:  55px;\n      line-height: 65px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h2 {\n      font-size:  65px;\n      line-height: 75px\n  }\n    }\n\n\n#page h3 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h3 {\n      font-size:  45px;\n      line-height: 57px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h3 {\n      font-size:  55px;\n      line-height: 68px\n  }\n    }\n\n\n#page h4 {\n    font-size: 26px;\n    line-height: 34px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h4 {\n      font-size:  37px;\n      line-height: 50px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h4 {\n      font-size:  45px;\n      line-height: 58px\n  }\n    }\n\n\n#page h5, #page h6, #page .h650, #page .h700, #page .h800, #page .h900, #page .h950 {\n    font-family: var(--font-body);\n    color: var(--color-black);\n  }\n\n\n#page h5 {\n    font-weight: 700;\n    font-size: 20px;\n    line-height: 28px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n#page h6 {\n    font-weight: 700;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h6 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h6 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h650 {\n    font-weight: 500;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h650 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h650 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h700 {\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h700 {\n      font-size:  16px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h700 {\n      font-size:  18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .h800 {\n    font-weight: 500;\n    font-size: 12px;\n    line-height: 16px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h800 {\n      font-size:  12px;\n      line-height: 16px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h800 {\n      font-size:  17px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h900 {\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h900 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h900 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h950 {\n    font-weight: 500;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h950 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h950 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page p {\n    font-family: var(--font-text);\n    font-weight: 400;\n    color: var(--color-black);\n  }\n\n\n#page .p-large {\n    font-size: 17px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-large {\n      font-size:  18px;\n      line-height: 28px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-large {\n      font-size:  20px;\n      line-height: 31px\n  }\n    }\n\n\n#page .p-medium {\n    font-size: 15px;\n    line-height: 22px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-medium {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-medium {\n      font-size:  17px;\n      line-height: 25px\n  }\n    }\n\n\n#page .p-small {\n    font-size: 13px;\n    line-height: 18px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-small {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-small {\n      font-size:  14px;\n      line-height: 18px\n  }\n    }\n\n\n#page .link {\n    color: var(--color-P500);\n    -webkit-text-decoration-line: underline;\n            text-decoration-line: underline;\n  }\n\n\n#page .link:hover {\n      -webkit-text-decoration-line: unset;\n              text-decoration-line: unset;\n    }\n\n\n#page .link:active {\n      color: var(--color-P300);\n    }\n\n\n#page .link:visited {\n      color: var(--color-P500);\n      -webkit-text-decoration-line: underline;\n              text-decoration-line: underline;\n    }\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 12.7786px;\n    gap: 8.52px;\n    height: 34.52px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n      height: 41.52px\n  }\n    }\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 10px;\n    gap: 8.52px;\n    height: 32px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n      height: 37px\n  }\n    }\n\n\n#page .tag-pink-large {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-pink-small {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-yellow-large {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-yellow-small {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-lightyellow-large {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .tag-lightyellow-small {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .primary-large-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 60px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 20px 35px;\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 23px;\n    border: 2px solid var(--color-black);\n    transition: all 0.5s;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-large-button {\n      padding: 25px 40px;\n      font-weight: 700;\n      font-size: 18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .primary-large-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-large-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .primary-small-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 40px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 10px 25px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n    transition: all 0.5s;\n    border: 2px solid var(--color-black);\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-small-button {\n      padding: 15px 40px;\n      font-weight: 700;\n      font-size: 16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .primary-small-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-small-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .secondary-button {\n    font-family: var(--font-body); \n    color: var(--color-black);\n    border-radius: 100px;\n    height: 52px;\n    border: 3px solid var(--color-black);\n    color: var(--color-black);\n    transition: all 0.5s;\n    padding: 15px 34px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 22px;\n    background: transparent;\n  }\n\n\n#page .secondary-button:hover {\n      background: var(--color-black);\n      color: var(--color-white);\n    }\n\n\n#page .secondary-button:active {\n      background: var(--color-G500);\n      border-color: var(--color-G500);\n    }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1nkmk8r', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link0 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true, crossorigin: true });
			link2 = claim_element(head_nodes, "LINK", { href: true, rel: true });
			link3 = claim_element(head_nodes, "LINK", { rel: true, type: true, href: true });
			script0 = claim_element(head_nodes, "SCRIPT", { type: true, src: true });
			var script0_nodes = children(script0);
			script0_nodes.forEach(detach);
			script1 = claim_element(head_nodes, "SCRIPT", { src: true });
			var script1_nodes = children(script1);
			script1_nodes.forEach(detach);

			link4 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			meta2 = claim_element(head_nodes, "META", { charset: true });
			meta3 = claim_element(head_nodes, "META", { name: true, content: true });
			meta4 = claim_element(head_nodes, "META", { name: true, content: true });
			meta5 = claim_element(head_nodes, "META", { name: true, content: true });
			meta6 = claim_element(head_nodes, "META", { name: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\n:root {\n  /* Fonts  */\n  --font-heading: 'Fraunces', serif;\n  --font-body: 'IBM Plex Mono', monospace;\n  --font-text: 'Work Sans', sans-serif;\n  \n  /* Colors */\n  --color-Y500: #E9D90A;\n  --color-Y400: #F6E500;\n  --color-Y300: #F7D254;\n  --color-Y200: #FFF587;\n  --color-Y100: #FFFCDA;\n\n  --color-P500: #E82884;\n  --color-P400: #FF4FA3;\n  --color-P300: #FF74B7;\n  --color-P200: #FFB1D7;\n  --color-P100: #FFD6E9;\n\n  --color-T500: #50ADBE;\n  --color-T400: #69C9DB;\n  --color-T300: #A8E1EC;\n  --color-T200: #C2F1FA;\n  --color-T100: #E2FAFF;\n\n  --color-G500: #C8C9DC;\n  --color-G400: #D5D7EF;\n  --color-G300: #E6E7FB;\n  --color-G200: #EEF2FD;\n  --color-G100: #F4F9FC;\n\n  --color-black: #000000;\n  --color-white: #FFFFFF;\n  \n  /* Base values */\n  --color-primary: var(--color-Y400);\n  --color-secondary: var(--color-P400);\n  --color-tertiary: var(--color-black);\n  --color-tertiary: var(--color-white);\n  \n  /* --color: var(--color-base);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --border-color: #eee;\n  --background: white; */\n  --border: 0.851905px solid var(--color-black);\n  --border-radius: 4.25952px;\n  --max-content-width-mobile: 768px;\n  --max-content-width-small-desktop: 900px;\n  --max-content-width: 1200px;\n  --page-padding-desktop: 90px 80px;\n  --page-padding-small-desktop: 120px 60px;\n  --page-padding-mobile: 90px 18px;\n\n  --hero-padding-desktop: 150px 80px 90px 80px;\n  --hero-padding-large-desktop: 200px 80px 90px 80px;\n\n  --hero-padding-mobile: 100px 18px 90px 18px;\n  --content-padding: 0px 50px;\n  \n}\n\n\n#page a {\n    color: var(--color-black);\n  }\n\n\n#page h1,#page h2,#page h3,#page h4 {\n    font-family: var(--font-heading);\n    font-weight: 700;\n    color: var(--color-black);\n  }\n\n\n#page h1 {\n    font-size: 33px;\n    line-height: 39px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h1 {\n      font-size:  67px;\n      line-height: 69px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h1 {\n      font-size:  83px;\n      line-height: 93px\n  }\n    }\n\n\n#page h2 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h2 {\n      font-size:  55px;\n      line-height: 65px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h2 {\n      font-size:  65px;\n      line-height: 75px\n  }\n    }\n\n\n#page h3 {\n    font-size: 28px;\n    line-height: 33px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h3 {\n      font-size:  45px;\n      line-height: 57px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h3 {\n      font-size:  55px;\n      line-height: 68px\n  }\n    }\n\n\n#page h4 {\n    font-size: 26px;\n    line-height: 34px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h4 {\n      font-size:  37px;\n      line-height: 50px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h4 {\n      font-size:  45px;\n      line-height: 58px\n  }\n    }\n\n\n#page h5, #page h6, #page .h650, #page .h700, #page .h800, #page .h900, #page .h950 {\n    font-family: var(--font-body);\n    color: var(--color-black);\n  }\n\n\n#page h5 {\n    font-weight: 700;\n    font-size: 20px;\n    line-height: 28px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h5 {\n      font-size:  30px;\n      line-height: 39px\n  }\n    }\n\n\n#page h6 {\n    font-weight: 700;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page h6 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page h6 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h650 {\n    font-weight: 500;\n    font-size: 18px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h650 {\n      font-size:  21px;\n      line-height: 29px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h650 {\n      font-size:  25px;\n      line-height: 33px\n  }\n    }\n\n\n#page .h700 {\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h700 {\n      font-size:  16px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h700 {\n      font-size:  18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .h800 {\n    font-weight: 500;\n    font-size: 12px;\n    line-height: 16px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h800 {\n      font-size:  12px;\n      line-height: 16px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h800 {\n      font-size:  17px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h900 {\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h900 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h900 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .h950 {\n    font-weight: 500;\n    font-size: 14px;\n    line-height: 20px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .h950 {\n      font-size:  14px;\n      line-height: 20px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .h950 {\n      font-size:  16px;\n      line-height: 22px\n  }\n    }\n\n\n#page p {\n    font-family: var(--font-text);\n    font-weight: 400;\n    color: var(--color-black);\n  }\n\n\n#page .p-large {\n    font-size: 17px;\n    line-height: 26px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-large {\n      font-size:  18px;\n      line-height: 28px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-large {\n      font-size:  20px;\n      line-height: 31px\n  }\n    }\n\n\n#page .p-medium {\n    font-size: 15px;\n    line-height: 22px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-medium {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-medium {\n      font-size:  17px;\n      line-height: 25px\n  }\n    }\n\n\n#page .p-small {\n    font-size: 13px;\n    line-height: 18px;\n  }\n\n\n@media only screen and (min-width: 1024px) {\n\n\n#page .p-small {\n      font-size:  15px;\n      line-height: 22px\n  }\n    }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .p-small {\n      font-size:  14px;\n      line-height: 18px\n  }\n    }\n\n\n#page .link {\n    color: var(--color-P500);\n    -webkit-text-decoration-line: underline;\n            text-decoration-line: underline;\n  }\n\n\n#page .link:hover {\n      -webkit-text-decoration-line: unset;\n              text-decoration-line: unset;\n    }\n\n\n#page .link:active {\n      color: var(--color-P300);\n    }\n\n\n#page .link:visited {\n      color: var(--color-P500);\n      -webkit-text-decoration-line: underline;\n              text-decoration-line: underline;\n    }\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 12.7786px;\n    gap: 8.52px;\n    height: 34.52px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-large,\n  #page .tag-yellow-large,\n  #page .tag-lightyellow-large {\n      height: 41.52px\n  }\n    }\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n    border-width: 2px;\n    border: var(--border);\n    border-radius: var(--border-radius);\n    padding: 0px 10px;\n    gap: 8.52px;\n    height: 32px;\n    width: -webkit-max-content;\n    width: -moz-max-content;\n    width: max-content;\n    display: flex;\n    align-items: center;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .tag-pink-small,\n  #page .tag-yellow-small,\n  #page .tag-lightyellow-small {\n      height: 37px\n  }\n    }\n\n\n#page .tag-pink-large {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-pink-small {\n    background-color: var(--color-secondary);\n  }\n\n\n#page .tag-yellow-large {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-yellow-small {\n    background-color: var(--color-primary);\n  }\n\n\n#page .tag-lightyellow-large {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .tag-lightyellow-small {\n    background-color: var(--color-Y100);\n  }\n\n\n#page .primary-large-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 60px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 20px 35px;\n    font-weight: 700;\n    font-size: 16px;\n    line-height: 23px;\n    border: 2px solid var(--color-black);\n    transition: all 0.5s;\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-large-button {\n      padding: 25px 40px;\n      font-weight: 700;\n      font-size: 18px;\n      line-height: 25px\n  }\n    }\n\n\n#page .primary-large-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-large-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .primary-small-button {\n    font-family: var(--font-body);\n    color: var(--color-black);\n    border-radius: 100px;\n    /* height: 40px; */\n    background-color: var(--color-black);\n    color: var(--color-white);\n    padding: 10px 25px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 20px;\n    transition: all 0.5s;\n    border: 2px solid var(--color-black);\n  }\n\n\n@media only screen and (min-width: 1440px) {\n\n\n#page .primary-small-button {\n      padding: 15px 40px;\n      font-weight: 700;\n      font-size: 16px;\n      line-height: 22px\n  }\n    }\n\n\n#page .primary-small-button:hover {\n      background: transparent;\n      color: var(--color-black);\n      border: 2px solid var(--color-black);\n    }\n\n\n#page .primary-small-button:active {\n      margin: -1px;\n      border: 3px solid var(--color-black);\n    }\n\n\n#page .secondary-button {\n    font-family: var(--font-body); \n    color: var(--color-black);\n    border-radius: 100px;\n    height: 52px;\n    border: 3px solid var(--color-black);\n    color: var(--color-black);\n    transition: all 0.5s;\n    padding: 15px 34px;\n    font-weight: 700;\n    font-size: 14px;\n    line-height: 22px;\n    background: transparent;\n  }\n\n\n#page .secondary-button:hover {\n      background: var(--color-black);\n      color: var(--color-white);\n    }\n\n\n#page .secondary-button:active {\n      background: var(--color-G500);\n      border-color: var(--color-G500);\n    }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link0, "rel", "preconnect");
			attr(link0, "href", "https://fonts.googleapis.com");
			attr(link1, "rel", "preconnect");
			attr(link1, "href", "https://fonts.gstatic.com");
			attr(link1, "crossorigin", "");
			attr(link2, "href", "https://fonts.googleapis.com/css2?family=Fraunces:wght@700&family=IBM+Plex+Mono:wght@500;700&family=Work+Sans&display=swap");
			attr(link2, "rel", "stylesheet");
			attr(link3, "rel", "stylesheet");
			attr(link3, "type", "text/css");
			attr(link3, "href", "https://cdn.jsdelivr.net/npm/toastify-js/src/toastify.min.css");
			attr(script0, "type", "text/javascript");
			if (!src_url_equal(script0.src, script0_src_value = "https://cdn.jsdelivr.net/npm/toastify-js")) attr(script0, "src", script0_src_value);
			if (!src_url_equal(script1.src, script1_src_value = "https://unpkg.com/@lottiefiles/lottie-player@1.5.7/dist/lottie-player.js")) attr(script1, "src", script1_src_value);
			attr(link4, "rel", "icon");
			attr(link4, "type", "image/png");
			attr(link4, "sizes", "32x32");
			attr(link4, "href", link4_href_value = /*favicon*/ ctx[0].url);
			document.title = "UNLOK Loyalty | Home";
			attr(meta2, "charset", "UTF-8");
			attr(meta3, "name", "description");
			attr(meta3, "content", "Unleash the Power of Blockchain Rewards");
			attr(meta4, "name", "keywords");
			attr(meta4, "content", "Blockchain, Crypto, Cryptocurrency, Unlok, Rewards, Staking, Loyalty Program, Earn, Redeem");
			attr(meta5, "name", "author");
			attr(meta5, "content", "Unlok Loyalty");
			attr(meta6, "name", "viewport");
			attr(meta6, "content", "width=device-width, initial-scale=1.0");
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, link2);
			append_hydration(document.head, link3);
			append_hydration(document.head, script0);
			append_hydration(document.head, script1);
			append_hydration(document.head, link4);
			append_hydration(document.head, meta2);
			append_hydration(document.head, meta3);
			append_hydration(document.head, meta4);
			append_hydration(document.head, meta5);
			append_hydration(document.head, meta6);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 1 && link4_href_value !== (link4_href_value = /*favicon*/ ctx[0].url)) {
				attr(link4, "href", link4_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link0);
			detach(link1);
			detach(link2);
			detach(link3);
			detach(script0);
			detach(script1);
			detach(link4);
			detach(meta2);
			detach(meta3);
			detach(meta4);
			detach(meta5);
			detach(meta6);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { favicon: 0 });
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i].link;
	return child_ctx;
}

// (254:35) 
function create_if_block_4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			attr(img, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (252:10) {#if logo.title}
function create_if_block_3(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (259:10) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let h6;
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_class_value;
	let a_href_value;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { class: true });
			var h6_nodes = children(h6);
			a = claim_element(h6_nodes, "A", { id: true, class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "id", "nav-item");

			attr(a, "class", a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"));

			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(h6, "class", "h950");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_class_value !== (a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"))) {
				attr(a, "class", a_class_value);
			}

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

// (273:35) 
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			attr(img, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (271:10) {#if logo.title}
function create_if_block_1$1(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (289:8) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t0;
	let a;
	let t1_value = /*site_nav_button*/ ctx[2].label + "";
	let t1;
	let a_href_value;
	let t2;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			a = element("a");
			t1 = text(t1_value);
			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t0 = claim_space(nav_nodes);
			a = claim_element(nav_nodes, "A", { class: true, id: true, href: true });
			var a_nodes = children(a);
			t1 = claim_text(a_nodes, t1_value);
			a_nodes.forEach(detach);
			t2 = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "primary-small-button");
			attr(a, "id", "nav");
			attr(a, "href", a_href_value = /*site_nav_button*/ ctx[2].url);
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-jc1u8d");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-jc1u8d");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t0);
			append_hydration(nav, a);
			append_hydration(a, t1);
			append_hydration(nav, t2);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[7]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*window, site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t0);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if ((!current || dirty & /*site_nav_button*/ 4) && t1_value !== (t1_value = /*site_nav_button*/ ctx[2].label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*site_nav_button*/ 4 && a_href_value !== (a_href_value = /*site_nav_button*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (292:14) {#each site_nav as { link }}
function create_each_block(ctx) {
	let h6;
	let a;
	let t_value = /*link*/ ctx[8].label + "";
	let t;
	let a_class_value;
	let a_href_value;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { class: true });
			var h6_nodes = children(h6);

			a = claim_element(h6_nodes, "A", {
				id: true,
				class: true,
				active: true,
				href: true
			});

			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "id", "nav-item");

			attr(a, "class", a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"));

			attr(a, "active", "true");
			attr(a, "href", a_href_value = /*link*/ ctx[8].url);
			attr(h6, "class", "h950");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[8].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_class_value !== (a_class_value = "" + (null_to_empty(window.location.pathname.includes(/*link*/ ctx[8].url)
			? 'active-link'
			: 'inactive-link') + " svelte-jc1u8d"))) {
				attr(a, "class", a_class_value);
			}

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[8].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

function create_fragment$2(ctx) {
	let div4;
	let header;
	let div3;
	let div2;
	let div0;
	let a0;
	let t0;
	let nav;
	let t1;
	let a1;
	let t2_value = /*site_nav_button*/ ctx[2].label + "";
	let t2;
	let a1_href_value;
	let t3;
	let div1;
	let a2;
	let t4;
	let button;
	let icon;
	let t5;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_3;
		if (/*logo*/ ctx[0].image.url) return create_if_block_4;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type && current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_1$1;
		if (/*logo*/ ctx[0].image.url) return create_if_block_2;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1 && current_block_type_1(ctx);

	icon = new Component$1({
			props: {
				height: "37",
				icon: "eva:menu-outline",
				style: "color:black;"
			}
		});

	let if_block2 = /*mobileNavOpen*/ ctx[3] && create_if_block$1(ctx);

	return {
		c() {
			div4 = element("div");
			header = element("header");
			div3 = element("div");
			div2 = element("div");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			a1 = element("a");
			t2 = text(t2_value);
			t3 = space();
			div1 = element("div");
			a2 = element("a");
			if (if_block1) if_block1.c();
			t4 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t5 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			header = claim_element(div4_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div3 = claim_element(header_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { style: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t1 = claim_space(nav_nodes);
			a1 = claim_element(nav_nodes, "A", { class: true, id: true, href: true });
			var a1_nodes = children(a1);
			t2 = claim_text(a1_nodes, t2_value);
			a1_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a2 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a2_nodes = children(a2);
			if (if_block1) if_block1.l(a2_nodes);
			a2_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t5 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-jc1u8d");
			attr(a1, "class", "primary-small-button");
			attr(a1, "id", "nav");
			attr(a1, "href", a1_href_value = /*site_nav_button*/ ctx[2].url);
			set_style(nav, "display", "flex");
			set_style(nav, "align-items", "center");
			attr(nav, "class", "svelte-jc1u8d");
			attr(div0, "class", "desktop-nav svelte-jc1u8d");
			attr(a2, "href", "/");
			attr(a2, "class", "logo svelte-jc1u8d");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-jc1u8d");
			attr(div2, "class", "section-container svelte-jc1u8d");
			attr(div3, "class", "header-container svelte-jc1u8d");
			attr(header, "class", "svelte-jc1u8d");
			attr(div4, "class", "section");
			attr(div4, "id", "section-f9cd5f20");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, header);
			append_hydration(header, div3);
			append_hydration(div3, div2);
			append_hydration(div2, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t1);
			append_hydration(nav, a1);
			append_hydration(a1, t2);
			append_hydration(div2, t3);
			append_hydration(div2, div1);
			append_hydration(div1, a2);
			if (if_block1) if_block1.m(a2, null);
			append_hydration(div1, t4);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t5);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if (if_block0) if_block0.d(1);
				if_block0 = current_block_type && current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*window, site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t1);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if ((!current || dirty & /*site_nav_button*/ 4) && t2_value !== (t2_value = /*site_nav_button*/ ctx[2].label + "")) set_data(t2, t2_value);

			if (!current || dirty & /*site_nav_button*/ 4 && a1_href_value !== (a1_href_value = /*site_nav_button*/ ctx[2].url)) {
				attr(a1, "href", a1_href_value);
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if (if_block1) if_block1.d(1);
				if_block1 = current_block_type_1 && current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a2, null);
				}
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$1(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);

			if (if_block0) {
				if_block0.d();
			}

			destroy_each(each_blocks, detaching);

			if (if_block1) {
				if_block1.d();
			}

			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { site_nav_button } = $$props;
	let mobileNavOpen = false;

	function toggleMobileNav() {
		$$invalidate(3, mobileNavOpen = !mobileNavOpen);

		if (mobileNavOpen) {
			document.body.style.overflow = 'hidden';
		} else {
			document.body.style.overflow = 'unset';
		}
	}

	const click_handler = () => toggleMobileNav();
	const click_handler_1 = () => toggleMobileNav();

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('site_nav_button' in $$props) $$invalidate(2, site_nav_button = $$props.site_nav_button);
	};

	return [
		logo,
		site_nav,
		site_nav_button,
		mobileNavOpen,
		toggleMobileNav,
		favicon,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			favicon: 5,
			logo: 0,
			site_nav: 1,
			site_nav_button: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[14] = list[i];
	return child_ctx;
}

// (572:12) {#each hero_feature as feature }
function create_each_block$1(ctx) {
	let div;
	let h6;
	let t0_value = /*feature*/ ctx[14].title + "";
	let t0;
	let t1;

	return {
		c() {
			div = element("div");
			h6 = element("h6");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			h6 = claim_element(div_nodes, "H6", { class: true });
			var h6_nodes = children(h6);
			t0 = claim_text(h6_nodes, t0_value);
			h6_nodes.forEach(detach);
			t1 = claim_space(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h6, "class", "h700");
			attr(div, "class", "tag-lightyellow-small");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, h6);
			append_hydration(h6, t0);
			append_hydration(div, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*hero_feature*/ 16 && t0_value !== (t0_value = /*feature*/ ctx[14].title + "")) set_data(t0, t0_value);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function create_fragment$3(ctx) {
	let div8;
	let section;
	let div7;
	let div6;
	let div0;
	let h10;
	let t0;
	let t1;
	let div1;
	let h11;
	let t2;
	let t3;
	let div3;
	let div2;
	let t4;
	let p;
	let t5;
	let t6;
	let div5;
	let div4;
	let lottie_player;
	let lottie_player_src_value;
	let t7;
	let img0;
	let img0_src_value;
	let img0_alt_value;
	let t8;
	let img1;
	let img1_src_value;
	let img1_alt_value;
	let t9;
	let img2;
	let img2_src_value;
	let img2_alt_value;
	let section_aria_label_value;
	let each_value = /*hero_feature*/ ctx[4];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div8 = element("div");
			section = element("section");
			div7 = element("div");
			div6 = element("div");
			div0 = element("div");
			h10 = element("h1");
			t0 = text(/*hero_title1*/ ctx[1]);
			t1 = space();
			div1 = element("div");
			h11 = element("h1");
			t2 = text(/*hero_title2*/ ctx[2]);
			t3 = space();
			div3 = element("div");
			div2 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t4 = space();
			p = element("p");
			t5 = text(/*hero_description*/ ctx[3]);
			t6 = space();
			div5 = element("div");
			div4 = element("div");
			lottie_player = element("lottie-player");
			t7 = space();
			img0 = element("img");
			t8 = space();
			img1 = element("img");
			t9 = space();
			img2 = element("img");
			this.h();
		},
		l(nodes) {
			div8 = claim_element(nodes, "DIV", { class: true, id: true });
			var div8_nodes = children(div8);

			section = claim_element(div8_nodes, "SECTION", {
				role: true,
				"aria-label": true,
				class: true
			});

			var section_nodes = children(section);
			div7 = claim_element(section_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div0 = claim_element(div6_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h10 = claim_element(div0_nodes, "H1", { class: true });
			var h10_nodes = children(h10);
			t0 = claim_text(h10_nodes, /*hero_title1*/ ctx[1]);
			h10_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div6_nodes);
			div1 = claim_element(div6_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h11 = claim_element(div1_nodes, "H1", { class: true });
			var h11_nodes = children(h11);
			t2 = claim_text(h11_nodes, /*hero_title2*/ ctx[2]);
			h11_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t3 = claim_space(div6_nodes);
			div3 = claim_element(div6_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div2_nodes);
			}

			div2_nodes.forEach(detach);
			t4 = claim_space(div3_nodes);
			p = claim_element(div3_nodes, "P", { class: true });
			var p_nodes = children(p);
			t5 = claim_text(p_nodes, /*hero_description*/ ctx[3]);
			p_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t6 = claim_space(div6_nodes);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);

			lottie_player = claim_element(div4_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player).forEach(detach);
			t7 = claim_space(div4_nodes);
			img0 = claim_element(div4_nodes, "IMG", { class: true, src: true, alt: true });
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			t8 = claim_space(div6_nodes);
			img1 = claim_element(div6_nodes, "IMG", { class: true, src: true, alt: true });
			t9 = claim_space(div6_nodes);
			img2 = claim_element(div6_nodes, "IMG", { class: true, src: true, alt: true });
			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h10, "class", "svelte-vn1x14");
			attr(div0, "class", "hero-text-container1 svelte-vn1x14");
			attr(h11, "class", "svelte-vn1x14");
			attr(div1, "class", "hero-text-container2 svelte-vn1x14");
			attr(div2, "class", "hero-feature-tag-container svelte-vn1x14");
			attr(p, "class", "h650 svelte-vn1x14");
			attr(div3, "class", "hero-feature-container svelte-vn1x14");
			set_custom_element_data(lottie_player, "autoplay", "");
			set_custom_element_data(lottie_player, "loop", "");
			set_custom_element_data(lottie_player, "mode", "normal");
			set_custom_element_data(lottie_player, "class", "hero-lottie svelte-vn1x14");
			if (!src_url_equal(lottie_player.src, lottie_player_src_value = coffeeLottie)) set_custom_element_data(lottie_player, "src", lottie_player_src_value);
			attr(img0, "class", "hero-image svelte-vn1x14");
			if (!src_url_equal(img0.src, img0_src_value = /*hero_image*/ ctx[5].url)) attr(img0, "src", img0_src_value);
			attr(img0, "alt", img0_alt_value = /*hero_image*/ ctx[5].alt);
			attr(div4, "class", "svelte-vn1x14");
			attr(div5, "class", "hero-image-wrapper svelte-vn1x14");
			attr(img1, "class", "home-banner-mobile svelte-vn1x14");
			if (!src_url_equal(img1.src, img1_src_value = /*home_banner_mobile*/ ctx[6].url)) attr(img1, "src", img1_src_value);
			attr(img1, "alt", img1_alt_value = /*home_banner_mobile*/ ctx[6].alt);
			attr(img2, "class", "home-banner-small-desktop svelte-vn1x14");
			if (!src_url_equal(img2.src, img2_src_value = /*home_banner_small_desktop*/ ctx[7].url)) attr(img2, "src", img2_src_value);
			attr(img2, "alt", img2_alt_value = /*home_banner_small_desktop*/ ctx[7].alt);
			attr(div6, "class", "header-wrapper svelte-vn1x14");
			attr(div7, "class", "header-container svelte-vn1x14");
			attr(section, "role", "img");
			attr(section, "aria-label", section_aria_label_value = /*background*/ ctx[0].alt);
			attr(section, "class", "svelte-vn1x14");
			attr(div8, "class", "section");
			attr(div8, "id", "section-5daad03b");
		},
		m(target, anchor) {
			insert_hydration(target, div8, anchor);
			append_hydration(div8, section);
			append_hydration(section, div7);
			append_hydration(div7, div6);
			append_hydration(div6, div0);
			append_hydration(div0, h10);
			append_hydration(h10, t0);
			append_hydration(div6, t1);
			append_hydration(div6, div1);
			append_hydration(div1, h11);
			append_hydration(h11, t2);
			append_hydration(div6, t3);
			append_hydration(div6, div3);
			append_hydration(div3, div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div2, null);
				}
			}

			append_hydration(div3, t4);
			append_hydration(div3, p);
			append_hydration(p, t5);
			append_hydration(div6, t6);
			append_hydration(div6, div5);
			append_hydration(div5, div4);
			append_hydration(div4, lottie_player);
			append_hydration(div4, t7);
			append_hydration(div4, img0);
			append_hydration(div6, t8);
			append_hydration(div6, img1);
			append_hydration(div6, t9);
			append_hydration(div6, img2);
		},
		p(ctx, [dirty]) {
			if (dirty & /*hero_title1*/ 2) set_data(t0, /*hero_title1*/ ctx[1]);
			if (dirty & /*hero_title2*/ 4) set_data(t2, /*hero_title2*/ ctx[2]);

			if (dirty & /*hero_feature*/ 16) {
				each_value = /*hero_feature*/ ctx[4];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div2, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*hero_description*/ 8) set_data(t5, /*hero_description*/ ctx[3]);

			if (dirty & /*hero_image*/ 32 && !src_url_equal(img0.src, img0_src_value = /*hero_image*/ ctx[5].url)) {
				attr(img0, "src", img0_src_value);
			}

			if (dirty & /*hero_image*/ 32 && img0_alt_value !== (img0_alt_value = /*hero_image*/ ctx[5].alt)) {
				attr(img0, "alt", img0_alt_value);
			}

			if (dirty & /*home_banner_mobile*/ 64 && !src_url_equal(img1.src, img1_src_value = /*home_banner_mobile*/ ctx[6].url)) {
				attr(img1, "src", img1_src_value);
			}

			if (dirty & /*home_banner_mobile*/ 64 && img1_alt_value !== (img1_alt_value = /*home_banner_mobile*/ ctx[6].alt)) {
				attr(img1, "alt", img1_alt_value);
			}

			if (dirty & /*home_banner_small_desktop*/ 128 && !src_url_equal(img2.src, img2_src_value = /*home_banner_small_desktop*/ ctx[7].url)) {
				attr(img2, "src", img2_src_value);
			}

			if (dirty & /*home_banner_small_desktop*/ 128 && img2_alt_value !== (img2_alt_value = /*home_banner_small_desktop*/ ctx[7].alt)) {
				attr(img2, "alt", img2_alt_value);
			}

			if (dirty & /*background*/ 1 && section_aria_label_value !== (section_aria_label_value = /*background*/ ctx[0].alt)) {
				attr(section, "aria-label", section_aria_label_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div8);
			destroy_each(each_blocks, detaching);
		}
	};
}

const coffeeLottie = '{"v":"5.5.7","meta":{"g":"LottieFiles AE 0.1.20","a":"","k":"","d":"","tc":""},"fr":25,"ip":0,"op":100,"w":1000,"h":1000,"nm":"Love_13_Two_Cups","ddd":0,"assets":[],"layers":[{"ddd":0,"ind":1,"ty":4,"nm":"Straw Left ","parent":3,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":1,"k":[{"i":{"x":[0.782],"y":[1]},"o":{"x":[0.861],"y":[0]},"t":12,"s":[0]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":27,"s":[-1]},{"i":{"x":[0.491],"y":[1]},"o":{"x":[0.527],"y":[0]},"t":37,"s":[6]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":47,"s":[-5]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":57,"s":[4]},{"i":{"x":[0.764],"y":[0.887]},"o":{"x":[0.478],"y":[0]},"t":67,"s":[-3]},{"i":{"x":[0.442],"y":[1]},"o":{"x":[0.272],"y":[-0.588]},"t":77,"s":[1.5]},{"t":92,"s":[0]}],"ix":10},"p":{"a":0,"k":[194.597,56.631,0],"ix":2},"a":{"a":0,"k":[143.587,205.958,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[42.428,77.979],[46.794,-33.457],[-46.794,-77.979]],"c":false},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[96.794,127.979],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":2,"ty":4,"nm":"Heart Left ","parent":3,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[199.616,336.065,0],"ix":2},"a":{"a":0,"k":[112.51,102.015,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[13.12,1.705],[0,0],[13.879,6.099],[6.787,-24.366],[0,0],[-9.449,33.92]],"o":[[-15.033,-1.955],[0,0],[-12.112,-5.322],[-9.45,33.92],[0,0],[6.787,-24.367]],"v":[[29.589,-35.524],[5.379,-26.158],[-10.504,-46.692],[-53.06,-26.775],[-16.398,52.015],[55.723,3.528]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[112.51,102.015],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":3,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":3,"ty":4,"nm":"Cup Left ","parent":4,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":1,"k":[{"i":{"x":[0.782],"y":[1]},"o":{"x":[0.861],"y":[0]},"t":10,"s":[0]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":25,"s":[-3]},{"i":{"x":[0.491],"y":[1]},"o":{"x":[0.527],"y":[0]},"t":35,"s":[10]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":45,"s":[-8]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":55,"s":[5]},{"i":{"x":[0.764],"y":[0.887]},"o":{"x":[0.478],"y":[0]},"t":65,"s":[-3]},{"i":{"x":[0.442],"y":[1]},"o":{"x":[0.272],"y":[-0.588]},"t":75,"s":[1.5]},{"t":90,"s":[0]}],"ix":10},"p":{"a":0,"k":[-220.436,29.428,0],"ix":2},"a":{"a":0,"k":[142.372,514.333,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[3.724,1.038],[0,0],[-1.037,3.724],[0,0],[-3.724,-1.038],[0,0],[1.037,-3.724],[0,0]],"o":[[0,0],[-3.724,-1.037],[0,0],[1.037,-3.724],[0,0],[3.725,1.037],[0,0],[-1.038,3.724]],"v":[[128.204,56.146],[-138.768,-18.223],[-143.633,-26.845],[-136.825,-51.282],[-128.204,-56.146],[138.768,18.223],[143.633,26.844],[136.826,51.281]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.685999971278,0.109999997008,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[250.073,148.087],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":3,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[2.806,0.782],[0,0],[1.469,-2.516],[0,0],[-4.046,-1.127],[0,0],[-0.063,4.2],[0,0]],"o":[[0,0],[-2.806,-0.781],[0,0],[-2.117,3.628],[0,0],[4.047,1.127],[0,0],[0.044,-2.913]],"v":[[120.281,4.584],[-96.253,-55.735],[-103.508,-52.792],[-122.896,-19.576],[-119.082,-10.171],[116.265,55.389],[124.393,49.311],[124.969,10.854]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[256.764,106.516],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[-0.063,4.2],[0,0],[0,0],[1.469,-2.515],[0,0]],"o":[[4.046,1.127],[0,0],[0,0],[-2.806,-0.782],[0,0],[0,0]],"v":[[106.111,43.025],[114.238,36.947],[114.568,14.864],[-94.484,-43.37],[-101.74,-40.428],[-114.568,-18.449]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.685999971278,0.109999997008,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[266.919,118.88],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[-0.063,4.2],[0,0],[2.806,0.782],[0,0],[1.469,-2.516],[0,0],[-4.045,-1.127],[0,0]],"o":[[0,0],[0.044,-2.913],[0,0],[-2.806,-0.781],[0,0],[-2.118,3.628],[0,0],[4.046,1.127]],"v":[[124.394,49.311],[124.97,10.854],[120.282,4.584],[-96.252,-55.735],[-103.507,-52.792],[-122.896,-19.576],[-119.082,-10.171],[116.266,55.389]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.830999995213,0.522000002394,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[256.763,106.516],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 4","np":2,"cix":2,"bm":0,"ix":4,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[3.219,0.896],[0,0],[-0.638,3.281],[0,0],[-3.603,-1.004],[0,0],[1.286,-3.512],[0,0]],"o":[[0,0],[-3.22,-0.898],[0,0],[0.715,-3.671],[0,0],[3.603,1.003],[0,0],[-1.15,3.138]],"v":[[83.074,116.168],[-141.971,53.48],[-146.542,46.081],[-115.951,-111.111],[-107.939,-116.061],[141.596,-46.548],[145.894,-38.171],[90.811,112.199]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[203.721,335.379],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 5","np":2,"cix":2,"bm":0,"ix":5,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0.714,-3.672],[0,0],[0,0],[-1.15,3.138],[0,0]],"o":[[-3.603,-1.003],[0,0],[0,0],[3.22,0.897],[0,0],[0,0]],"v":[[-94.99,-96.82],[-103.001,-91.87],[-128.736,40.365],[74.309,96.926],[82.047,92.957],[128.737,-34.498]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.685999971278,0.109999997008,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[212.485,354.621],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 6","np":2,"cix":2,"bm":0,"ix":6,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[3.603,1.003],[0,0],[0.714,-3.671],[0,0],[-3.22,-0.897],[0,0],[-1.15,3.138],[0,0]],"o":[[0,0],[-3.603,-1.003],[0,0],[-0.639,3.281],[0,0],[3.22,0.896],[0,0],[1.286,-3.512]],"v":[[141.597,-46.549],[-107.94,-116.062],[-115.95,-111.111],[-146.542,46.081],[-141.971,53.479],[83.073,116.168],[90.811,112.199],[145.895,-38.17]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.830999995213,0.522000002394,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[203.72,335.38],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 7","np":2,"cix":2,"bm":0,"ix":7,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[14.098,3.928],[0,0],[-2.857,14.354],[0,0],[-3.382,-0.942],[0,0],[1.194,-3.301],[0,0]],"o":[[0,0],[-14.098,-3.926],[0,0],[0.685,-3.442],[0,0],[3.381,0.942],[0,0],[-4.976,13.762]],"v":[[11.51,200.984],[-136.938,159.631],[-156.868,127.221],[-91.88,-199.337],[-84.346,-203.97],[154.478,-137.442],[158.531,-129.58],[45.327,183.547]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[209.725,337.754],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 8","np":2,"cix":2,"bm":0,"ix":8,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0.728,-3.658],[0,0],[-2.35,-0.655],[0,0],[-5.738,15.873],[0,0]],"o":[[-3.593,-1.001],[0,0],[2.069,1.112],[0,0],[16.259,4.53],[0,0],[0,0]],"v":[[-73.129,-186.755],[-81.134,-181.832],[-145.448,141.335],[-138.814,144.009],[1.971,183.226],[40.971,163.115],[145.448,-125.867]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[215.433,354.444],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 9","np":2,"cix":2,"bm":0,"ix":9,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[3.593,1],[0,0],[0.728,-3.658],[0,0],[-16.26,-4.53],[0,0],[-5.738,15.873],[0,0]],"o":[[0,0],[-3.593,-1.001],[0,0],[-3.295,16.554],[0,0],[16.26,4.53],[0,0],[1.268,-3.508]],"v":[[153.95,-137.343],[-84.091,-203.653],[-92.096,-198.73],[-156.229,123.528],[-133.243,160.907],[7.54,200.124],[46.542,180.013],[158.256,-128.99]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.39199999641,0.596000043084,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[209.863,337.547],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 10","np":2,"cix":2,"bm":0,"ix":10,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":4,"ty":3,"nm":"Position Controller 2","sr":1,"ks":{"o":{"a":0,"k":0,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[501.607,763.989,0],"to":[0,0,0],"ti":[0,0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":47,"s":[501.607,699.989,0],"to":[0,0,0],"ti":[0,0,0]},{"t":100,"s":[501.607,763.989,0]}],"ix":2},"a":{"a":0,"k":[50,50,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"ip":0,"op":100,"st":-2,"bm":0},{"ddd":0,"ind":5,"ty":4,"nm":"Heart Right ","parent":7,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":0,"k":[242.009,335.575,0],"ix":2},"a":{"a":0,"k":[112.225,101.945,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[12.213,-5.086],[0,0],[15.069,-1.661],[-6.311,-24.494],[0,0],[8.786,34.098]],"o":[[-13.995,5.827],[0,0],[-13.15,1.45],[8.786,34.098],[0,0],[-6.31,-24.494]],"v":[[11.276,-46.859],[-5.003,-26.637],[-29.027,-36.475],[-55.914,2.059],[15.244,51.945],[53.439,-26.117]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.685999971278,0.109999997008,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[112.225,101.945],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":3,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":6,"ty":4,"nm":"Straw Right ","parent":7,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":1,"k":[{"i":{"x":[0.782],"y":[1]},"o":{"x":[0.861],"y":[0]},"t":16,"s":[0]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":31,"s":[-1]},{"i":{"x":[0.491],"y":[1]},"o":{"x":[0.527],"y":[0]},"t":41,"s":[6]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":51,"s":[-5]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":61,"s":[4]},{"i":{"x":[0.764],"y":[0.887]},"o":{"x":[0.478],"y":[0]},"t":71,"s":[-3]},{"i":{"x":[0.442],"y":[1]},"o":{"x":[0.272],"y":[-0.588]},"t":81,"s":[1.5]},{"t":96,"s":[0]}],"ix":10},"p":{"a":0,"k":[244.538,53.132,0],"ix":2},"a":{"a":0,"k":[50,205.958,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[-42.427,77.979],[-46.793,-33.457],[46.793,-77.979]],"c":false},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[96.793,127.979],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":2,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":7,"ty":4,"nm":"Cup Right ","parent":8,"sr":1,"ks":{"o":{"a":0,"k":100,"ix":11},"r":{"a":1,"k":[{"i":{"x":[0.782],"y":[1]},"o":{"x":[0.861],"y":[0]},"t":14,"s":[0]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":28.25,"s":[-3]},{"i":{"x":[0.491],"y":[1]},"o":{"x":[0.527],"y":[0]},"t":37.75,"s":[10]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":47.25,"s":[-8]},{"i":{"x":[0.667],"y":[1]},"o":{"x":[0.333],"y":[0]},"t":56.75,"s":[5]},{"i":{"x":[0.764],"y":[0.887]},"o":{"x":[0.478],"y":[0]},"t":66.25,"s":[-3]},{"i":{"x":[0.442],"y":[1]},"o":{"x":[0.272],"y":[-0.588]},"t":75.75,"s":[1.5]},{"t":90,"s":[0]}],"ix":10},"p":{"a":0,"k":[354.003,132.417,0],"ix":2},"a":{"a":0,"k":[324.533,516.297,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"shapes":[{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[3.743,-0.964],[0,0],[0.963,3.744],[0,0],[-3.744,0.964],[0,0],[-0.965,-3.744],[0,0]],"o":[[0,0],[-3.743,0.965],[0,0],[-0.964,-3.744],[0,0],[3.744,-0.965],[0,0],[0.964,3.744]],"v":[[139.097,-15.513],[-129.274,53.635],[-137.798,48.603],[-144.129,24.038],[-139.096,15.513],[129.274,-53.635],[137.799,-48.603],[144.129,-24.038]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":1,"lj":1,"ml":10,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[195.093,146.267],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 1","np":3,"cix":2,"bm":0,"ix":1,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[2.821,-0.727],[0,0],[0.014,-2.913],[0,0],[-4.068,1.048],[0,0],[2.045,3.668],[0,0]],"o":[[0,0],[-2.82,0.727],[0,0],[-0.02,4.2],[0,0],[4.067,-1.048],[0,0],[-1.419,-2.543]],"v":[[97.346,-53.639],[-120.323,2.445],[-125.133,8.622],[-125.306,47.083],[-117.299,53.318],[119.283,-7.639],[123.281,-16.967],[104.542,-50.556]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[189.191,104.366],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 2","np":2,"cix":2,"bm":0,"ix":2,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[2.046,3.668],[0,0],[0,0],[0.014,-2.912],[0,0]],"o":[[4.067,-1.048],[0,0],[0,0],[-2.82,0.726],[0,0],[0,0]],"v":[[107.897,-14.272],[111.895,-23.599],[101.134,-42.887],[-109.015,11.26],[-113.825,17.436],[-113.94,42.887]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[200.577,110.999],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 3","np":2,"cix":2,"bm":0,"ix":3,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[2.046,3.668],[0,0],[2.822,-0.726],[0,0],[0.013,-2.913],[0,0],[-4.067,1.048],[0,0]],"o":[[0,0],[-1.42,-2.544],[0,0],[-2.82,0.727],[0,0],[-0.019,4.2],[0,0],[4.067,-1.048]],"v":[[123.28,-16.968],[104.542,-50.555],[97.345,-53.64],[-120.324,2.445],[-125.133,8.622],[-125.307,47.083],[-117.3,53.317],[119.282,-7.64]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.39199999641,0.596000043084,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[189.191,104.366],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 4","np":2,"cix":2,"bm":0,"ix":4,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[3.236,-0.834],[0,0],[1.088,3.16],[0,0],[-3.622,0.934],[0,0],[-0.642,-3.685],[0,0]],"o":[[0,0],[-3.236,0.834],[0,0],[-1.218,-3.536],[0,0],[3.621,-0.933],[0,0],[0.574,3.293]],"v":[[140.977,55.991],[-85.249,114.28],[-92.907,110.159],[-145.047,-41.256],[-140.587,-49.548],[110.258,-114.18],[118.17,-109.075],[145.691,48.682]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[237.71,334.675],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 5","np":2,"cix":2,"bm":0,"ix":5,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[-1.218,-3.536],[0,0],[0,0],[0.574,3.292],[0,0]],"o":[[-3.621,0.933],[0,0],[0,0],[3.237,-0.834],[0,0],[0,0]],"v":[[-121.561,-38.861],[-126.021,-30.569],[-82.16,96.808],[121.951,44.217],[126.665,36.91],[103.337,-96.808]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.043000000598,0.361000001197,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[256.736,346.448],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 6","np":2,"cix":2,"bm":0,"ix":6,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[3.621,-0.934],[0,0],[-1.217,-3.536],[0,0],[-3.236,0.833],[0,0],[0.574,3.293],[0,0]],"o":[[0,0],[-3.621,0.933],[0,0],[1.088,3.16],[0,0],[3.237,-0.834],[0,0],[-0.642,-3.684]],"v":[[110.258,-114.179],[-140.588,-49.547],[-145.048,-41.254],[-92.907,110.16],[-85.249,114.281],[140.976,55.992],[145.691,48.684],[118.17,-109.075]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.39199999641,0.596000043084,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[237.71,334.674],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 7","np":2,"cix":2,"bm":0,"ix":7,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[14.172,-3.651],[0,0],[4.707,13.858],[0,0],[-3.4,0.875],[0,0],[-0.618,-3.455],[0,0]],"o":[[0,0],[-14.171,3.652],[0,0],[-1.129,-3.323],[0,0],[3.398,-0.876],[0,0],[2.576,14.407]],"v":[[133.883,161.666],[-15.344,200.115],[-48.813,182.021],[-155.889,-133.254],[-151.682,-141.034],[88.393,-202.892],[95.835,-198.113],[154.442,129.651]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"st","c":{"a":0,"k":[0,0,0,1],"ix":3},"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":20,"ix":5},"lc":2,"lj":2,"bm":0,"nm":"Stroke 1","mn":"ADBE Vector Graphic - Stroke","hd":false},{"ty":"tr","p":{"a":0,"k":[231.65,337.291],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 8","np":2,"cix":2,"bm":0,"ix":8,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[0,0],[-1.199,-3.532],[0,0],[-2.363,0.608],[0,0],[2.971,16.615],[0,0]],"o":[[-3.611,0.931],[0,0],[2.347,-0.073],[0,0],[16.344,-4.211],[0,0],[0,0]],"v":[[-135.556,-131.828],[-140.026,-123.56],[-34.061,188.441],[-26.978,187.438],[114.544,150.973],[138.255,114.05],[84.166,-188.441]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.685999971278,0.109999997008,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[247.138,348.977],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 9","np":2,"cix":2,"bm":0,"ix":9,"mn":"ADBE Vector Group","hd":false},{"ty":"gr","it":[{"ind":0,"ty":"sh","ix":1,"ks":{"a":0,"k":{"i":[[3.611,-0.93],[0,0],[-1.199,-3.531],[0,0],[-16.345,4.211],[0,0],[2.972,16.616],[0,0]],"o":[[0,0],[-3.61,0.931],[0,0],[5.428,15.981],[0,0],[16.345,-4.211],[0,0],[-0.656,-3.671]],"v":[[88.122,-202.597],[-151.168,-140.942],[-155.637,-132.675],[-49.97,178.449],[-11.368,199.317],[130.154,162.852],[153.864,125.929],[96.029,-197.519]],"c":true},"ix":2},"nm":"Path 1","mn":"ADBE Vector Shape - Group","hd":false},{"ty":"fl","c":{"a":0,"k":[1,0.830999995213,0.522000002394,1],"ix":4},"o":{"a":0,"k":100,"ix":5},"r":1,"bm":0,"nm":"Fill 1","mn":"ADBE Vector Graphic - Fill","hd":false},{"ty":"tr","p":{"a":0,"k":[231.528,337.098],"ix":2},"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"r":{"a":0,"k":0,"ix":6},"o":{"a":0,"k":100,"ix":7},"sk":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0,"ix":5},"nm":"Transform"}],"nm":"Group 10","np":2,"cix":2,"bm":0,"ix":10,"mn":"ADBE Vector Group","hd":false}],"ip":0,"op":100,"st":0,"bm":0},{"ddd":0,"ind":8,"ty":3,"nm":"Position Controller","sr":1,"ks":{"o":{"a":0,"k":0,"ix":11},"r":{"a":0,"k":0,"ix":10},"p":{"a":1,"k":[{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":0,"s":[501.607,763.989,0],"to":[0,0,0],"ti":[0,0,0]},{"i":{"x":0.667,"y":1},"o":{"x":0.333,"y":0},"t":53,"s":[501.607,743.989,0],"to":[0,0,0],"ti":[0,0,0]},{"t":100,"s":[501.607,763.989,0]}],"ix":2},"a":{"a":0,"k":[50,50,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6}},"ao":0,"ip":0,"op":100,"st":-2,"bm":0}],"markers":[]}';

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { background } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { site_nav_button } = $$props;
	let { hero_title1 } = $$props;
	let { hero_title2 } = $$props;
	let { hero_description } = $$props;
	let { hero_feature } = $$props;
	let { hero_image } = $$props;
	let { home_banner_mobile } = $$props;
	let { home_banner_small_desktop } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(8, favicon = $$props.favicon);
		if ('background' in $$props) $$invalidate(0, background = $$props.background);
		if ('logo' in $$props) $$invalidate(9, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(10, site_nav = $$props.site_nav);
		if ('site_nav_button' in $$props) $$invalidate(11, site_nav_button = $$props.site_nav_button);
		if ('hero_title1' in $$props) $$invalidate(1, hero_title1 = $$props.hero_title1);
		if ('hero_title2' in $$props) $$invalidate(2, hero_title2 = $$props.hero_title2);
		if ('hero_description' in $$props) $$invalidate(3, hero_description = $$props.hero_description);
		if ('hero_feature' in $$props) $$invalidate(4, hero_feature = $$props.hero_feature);
		if ('hero_image' in $$props) $$invalidate(5, hero_image = $$props.hero_image);
		if ('home_banner_mobile' in $$props) $$invalidate(6, home_banner_mobile = $$props.home_banner_mobile);
		if ('home_banner_small_desktop' in $$props) $$invalidate(7, home_banner_small_desktop = $$props.home_banner_small_desktop);
	};

	return [
		background,
		hero_title1,
		hero_title2,
		hero_description,
		hero_feature,
		hero_image,
		home_banner_mobile,
		home_banner_small_desktop,
		favicon,
		logo,
		site_nav,
		site_nav_button
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 8,
			background: 0,
			logo: 9,
			site_nav: 10,
			site_nav_button: 11,
			hero_title1: 1,
			hero_title2: 2,
			hero_description: 3,
			hero_feature: 4,
			hero_image: 5,
			home_banner_mobile: 6,
			home_banner_small_desktop: 7
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$4(ctx) {
	let div4;
	let div3;
	let div2;
	let h3;
	let t0;
	let t1;
	let div1;
	let div0;
	let p0;
	let t2;
	let t3;
	let a0;
	let t4_value = /*action_button*/ ctx[3].label + "";
	let t4;
	let a0_href_value;
	let t5;
	let p1;
	let t6;
	let t7;
	let a1;
	let t8_value = /*action_button*/ ctx[3].label + "";
	let t8;
	let a1_href_value;

	return {
		c() {
			div4 = element("div");
			div3 = element("div");
			div2 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title*/ ctx[0]);
			t1 = space();
			div1 = element("div");
			div0 = element("div");
			p0 = element("p");
			t2 = text(/*content_paragraph_1*/ ctx[1]);
			t3 = space();
			a0 = element("a");
			t4 = text(t4_value);
			t5 = space();
			p1 = element("p");
			t6 = text(/*content_paragraph_2*/ ctx[2]);
			t7 = space();
			a1 = element("a");
			t8 = text(t8_value);
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h3 = claim_element(div2_nodes, "H3", {});
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			p0 = claim_element(div0_nodes, "P", { id: true, class: true });
			var p0_nodes = children(p0);
			t2 = claim_text(p0_nodes, /*content_paragraph_1*/ ctx[1]);
			p0_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);

			a0 = claim_element(div0_nodes, "A", {
				target: true,
				rel: true,
				class: true,
				href: true
			});

			var a0_nodes = children(a0);
			t4 = claim_text(a0_nodes, t4_value);
			a0_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(div1_nodes);
			p1 = claim_element(div1_nodes, "P", { class: true });
			var p1_nodes = children(p1);
			t6 = claim_text(p1_nodes, /*content_paragraph_2*/ ctx[2]);
			p1_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t7 = claim_space(div3_nodes);
			a1 = claim_element(div3_nodes, "A", { class: true, href: true });
			var a1_nodes = children(a1);
			t8 = claim_text(a1_nodes, t8_value);
			a1_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p0, "id", "content-paragraph-1");
			attr(p0, "class", "p-large svelte-eo207p");
			attr(a0, "target", "_blank");
			attr(a0, "rel", "noopener noreferrer");
			attr(a0, "class", "secondary-button svelte-eo207p");
			attr(a0, "href", a0_href_value = /*action_button*/ ctx[3].url);
			attr(div0, "class", "svelte-eo207p");
			attr(p1, "class", "p-large");
			attr(div1, "class", "svelte-eo207p");
			attr(div2, "class", "section-container content svelte-eo207p");
			attr(a1, "class", "secondary-button svelte-eo207p");
			attr(a1, "href", a1_href_value = /*action_button*/ ctx[3].url);
			attr(div3, "class", "wrapper svelte-eo207p");
			attr(div4, "class", "section");
			attr(div4, "id", "section-4538f64b");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
			append_hydration(div3, div2);
			append_hydration(div2, h3);
			append_hydration(h3, t0);
			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			append_hydration(div0, p0);
			append_hydration(p0, t2);
			append_hydration(div0, t3);
			append_hydration(div0, a0);
			append_hydration(a0, t4);
			append_hydration(div1, t5);
			append_hydration(div1, p1);
			append_hydration(p1, t6);
			append_hydration(div3, t7);
			append_hydration(div3, a1);
			append_hydration(a1, t8);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title*/ 1) set_data(t0, /*content_title*/ ctx[0]);
			if (dirty & /*content_paragraph_1*/ 2) set_data(t2, /*content_paragraph_1*/ ctx[1]);
			if (dirty & /*action_button*/ 8 && t4_value !== (t4_value = /*action_button*/ ctx[3].label + "")) set_data(t4, t4_value);

			if (dirty & /*action_button*/ 8 && a0_href_value !== (a0_href_value = /*action_button*/ ctx[3].url)) {
				attr(a0, "href", a0_href_value);
			}

			if (dirty & /*content_paragraph_2*/ 4) set_data(t6, /*content_paragraph_2*/ ctx[2]);
			if (dirty & /*action_button*/ 8 && t8_value !== (t8_value = /*action_button*/ ctx[3].label + "")) set_data(t8, t8_value);

			if (dirty & /*action_button*/ 8 && a1_href_value !== (a1_href_value = /*action_button*/ ctx[3].url)) {
				attr(a1, "href", a1_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div4);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_paragraph_1 } = $$props;
	let { content_paragraph_2 } = $$props;
	let { action_button } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_paragraph_1' in $$props) $$invalidate(1, content_paragraph_1 = $$props.content_paragraph_1);
		if ('content_paragraph_2' in $$props) $$invalidate(2, content_paragraph_2 = $$props.content_paragraph_2);
		if ('action_button' in $$props) $$invalidate(3, action_button = $$props.action_button);
	};

	return [
		content_title,
		content_paragraph_1,
		content_paragraph_2,
		action_button,
		favicon
	];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			favicon: 4,
			content_title: 0,
			content_paragraph_1: 1,
			content_paragraph_2: 2,
			action_button: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$5(ctx) {
	let div5;
	let div4;
	let div3;
	let div0;
	let h3;
	let t0;
	let t1;
	let p;
	let t2;
	let t3;
	let div1;
	let img0;
	let img0_src_value;
	let img0_alt_value;
	let t4;
	let img1;
	let img1_src_value;
	let img1_alt_value;
	let t5;
	let div2;
	let a;
	let t6_value = /*action_button*/ ctx[4].label + "";
	let t6;
	let a_href_value;

	return {
		c() {
			div5 = element("div");
			div4 = element("div");
			div3 = element("div");
			div0 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title*/ ctx[0]);
			t1 = space();
			p = element("p");
			t2 = text(/*content_paragraph_1*/ ctx[1]);
			t3 = space();
			div1 = element("div");
			img0 = element("img");
			t4 = space();
			img1 = element("img");
			t5 = space();
			div2 = element("div");
			a = element("a");
			t6 = text(t6_value);
			this.h();
		},
		l(nodes) {
			div5 = claim_element(nodes, "DIV", { class: true, id: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h3 = claim_element(div0_nodes, "H3", {});
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			p = claim_element(div0_nodes, "P", { class: true });
			var p_nodes = children(p);
			t2 = claim_text(p_nodes, /*content_paragraph_1*/ ctx[1]);
			p_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div3_nodes);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			img0 = claim_element(div1_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			div1_nodes.forEach(detach);
			t4 = claim_space(div3_nodes);

			img1 = claim_element(div3_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			t5 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			a = claim_element(div2_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t6 = claim_text(a_nodes, t6_value);
			a_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p, "class", "p-large");
			attr(div0, "class", "section-container content svelte-y3xae3");
			attr(img0, "id", "content-image-desktop");
			if (!src_url_equal(img0.src, img0_src_value = /*content_image_desktop*/ ctx[2].url)) attr(img0, "src", img0_src_value);
			attr(img0, "alt", img0_alt_value = /*content_image_desktop*/ ctx[2].alt);
			attr(img0, "class", "svelte-y3xae3");
			attr(div1, "class", "content-image-wrapper svelte-y3xae3");
			attr(img1, "id", "content-image-mobile");
			if (!src_url_equal(img1.src, img1_src_value = /*content_image_mobile*/ ctx[3].url)) attr(img1, "src", img1_src_value);
			attr(img1, "alt", img1_alt_value = /*content_image_mobile*/ ctx[3].alt);
			attr(img1, "class", "svelte-y3xae3");
			attr(a, "class", "primary-large-button svelte-y3xae3");
			attr(a, "href", a_href_value = /*action_button*/ ctx[4].url);
			attr(div2, "class", "button-wrapper svelte-y3xae3");
			attr(div3, "class", "wrapper svelte-y3xae3");
			attr(div4, "class", "container svelte-y3xae3");
			attr(div5, "class", "section");
			attr(div5, "id", "section-1b4f2208");
		},
		m(target, anchor) {
			insert_hydration(target, div5, anchor);
			append_hydration(div5, div4);
			append_hydration(div4, div3);
			append_hydration(div3, div0);
			append_hydration(div0, h3);
			append_hydration(h3, t0);
			append_hydration(div0, t1);
			append_hydration(div0, p);
			append_hydration(p, t2);
			append_hydration(div3, t3);
			append_hydration(div3, div1);
			append_hydration(div1, img0);
			append_hydration(div3, t4);
			append_hydration(div3, img1);
			append_hydration(div3, t5);
			append_hydration(div3, div2);
			append_hydration(div2, a);
			append_hydration(a, t6);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title*/ 1) set_data(t0, /*content_title*/ ctx[0]);
			if (dirty & /*content_paragraph_1*/ 2) set_data(t2, /*content_paragraph_1*/ ctx[1]);

			if (dirty & /*content_image_desktop*/ 4 && !src_url_equal(img0.src, img0_src_value = /*content_image_desktop*/ ctx[2].url)) {
				attr(img0, "src", img0_src_value);
			}

			if (dirty & /*content_image_desktop*/ 4 && img0_alt_value !== (img0_alt_value = /*content_image_desktop*/ ctx[2].alt)) {
				attr(img0, "alt", img0_alt_value);
			}

			if (dirty & /*content_image_mobile*/ 8 && !src_url_equal(img1.src, img1_src_value = /*content_image_mobile*/ ctx[3].url)) {
				attr(img1, "src", img1_src_value);
			}

			if (dirty & /*content_image_mobile*/ 8 && img1_alt_value !== (img1_alt_value = /*content_image_mobile*/ ctx[3].alt)) {
				attr(img1, "alt", img1_alt_value);
			}

			if (dirty & /*action_button*/ 16 && t6_value !== (t6_value = /*action_button*/ ctx[4].label + "")) set_data(t6, t6_value);

			if (dirty & /*action_button*/ 16 && a_href_value !== (a_href_value = /*action_button*/ ctx[4].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div5);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_paragraph_1 } = $$props;
	let { content_image_desktop } = $$props;
	let { content_image_mobile } = $$props;
	let { action_button } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_paragraph_1' in $$props) $$invalidate(1, content_paragraph_1 = $$props.content_paragraph_1);
		if ('content_image_desktop' in $$props) $$invalidate(2, content_image_desktop = $$props.content_image_desktop);
		if ('content_image_mobile' in $$props) $$invalidate(3, content_image_mobile = $$props.content_image_mobile);
		if ('action_button' in $$props) $$invalidate(4, action_button = $$props.action_button);
	};

	return [
		content_title,
		content_paragraph_1,
		content_image_desktop,
		content_image_mobile,
		action_button,
		favicon
	];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			favicon: 5,
			content_title: 0,
			content_paragraph_1: 1,
			content_image_desktop: 2,
			content_image_mobile: 3,
			action_button: 4
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$6(ctx) {
	let div6;
	let div5;
	let div4;
	let div3;
	let div0;
	let lottie_player;
	let lottie_player_src_value;
	let t0;
	let div2;
	let h3;
	let t1;
	let t2;
	let p;
	let t3;
	let t4;
	let div1;
	let a;
	let t5_value = /*action_button*/ ctx[2].label + "";
	let t5;
	let a_href_value;

	return {
		c() {
			div6 = element("div");
			div5 = element("div");
			div4 = element("div");
			div3 = element("div");
			div0 = element("div");
			lottie_player = element("lottie-player");
			t0 = space();
			div2 = element("div");
			h3 = element("h3");
			t1 = text(/*content_title*/ ctx[0]);
			t2 = space();
			p = element("p");
			t3 = text(/*content_paragraph_1*/ ctx[1]);
			t4 = space();
			div1 = element("div");
			a = element("a");
			t5 = text(t5_value);
			this.h();
		},
		l(nodes) {
			div6 = claim_element(nodes, "DIV", { class: true, id: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			lottie_player = claim_element(div0_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player).forEach(detach);
			div0_nodes.forEach(detach);
			t0 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", {});
			var div2_nodes = children(div2);
			h3 = claim_element(div2_nodes, "H3", {});
			var h3_nodes = children(h3);
			t1 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t2 = claim_space(div2_nodes);
			p = claim_element(div2_nodes, "P", { class: true });
			var p_nodes = children(p);
			t3 = claim_text(p_nodes, /*content_paragraph_1*/ ctx[1]);
			p_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a = claim_element(div1_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t5 = claim_text(a_nodes, t5_value);
			a_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_custom_element_data(lottie_player, "autoplay", "");
			set_custom_element_data(lottie_player, "loop", "");
			set_custom_element_data(lottie_player, "mode", "normal");
			set_custom_element_data(lottie_player, "class", "lottie svelte-w0psos");
			if (!src_url_equal(lottie_player.src, lottie_player_src_value = shapesLottie)) set_custom_element_data(lottie_player, "src", lottie_player_src_value);
			attr(div0, "class", "lottie-wrapper svelte-w0psos");
			attr(p, "class", "p-large");
			attr(a, "class", "primary-large-button svelte-w0psos");
			attr(a, "href", a_href_value = /*action_button*/ ctx[2].url);
			attr(div1, "class", "button-wrapper svelte-w0psos");
			attr(div3, "class", "section-container content svelte-w0psos");
			attr(div4, "class", "wrapper svelte-w0psos");
			attr(div5, "class", "container svelte-w0psos");
			attr(div6, "class", "section");
			attr(div6, "id", "section-5be993b2");
		},
		m(target, anchor) {
			insert_hydration(target, div6, anchor);
			append_hydration(div6, div5);
			append_hydration(div5, div4);
			append_hydration(div4, div3);
			append_hydration(div3, div0);
			append_hydration(div0, lottie_player);
			append_hydration(div3, t0);
			append_hydration(div3, div2);
			append_hydration(div2, h3);
			append_hydration(h3, t1);
			append_hydration(div2, t2);
			append_hydration(div2, p);
			append_hydration(p, t3);
			append_hydration(div2, t4);
			append_hydration(div2, div1);
			append_hydration(div1, a);
			append_hydration(a, t5);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title*/ 1) set_data(t1, /*content_title*/ ctx[0]);
			if (dirty & /*content_paragraph_1*/ 2) set_data(t3, /*content_paragraph_1*/ ctx[1]);
			if (dirty & /*action_button*/ 4 && t5_value !== (t5_value = /*action_button*/ ctx[2].label + "")) set_data(t5, t5_value);

			if (dirty & /*action_button*/ 4 && a_href_value !== (a_href_value = /*action_button*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div6);
		}
	};
}

const shapesLottie = '{"nm":"4 shapes","ddd":0,"h":512,"w":512,"meta":{"g":"@lottiefiles/toolkit-js 0.26.1"},"layers":[{"ty":0,"nm":"all the layers","sr":1,"st":180,"op":250,"ip":180,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[256,256,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[256,256,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"w":512,"h":512,"refId":"comp_0","ind":1},{"ty":0,"nm":"all the layers","sr":1,"st":120,"op":180,"ip":120,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[256,256,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[256,256,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"w":512,"h":512,"refId":"comp_0","ind":2},{"ty":0,"nm":"all the layers","sr":1,"st":60,"op":120,"ip":60,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[256,256,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[256,256,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"w":512,"h":512,"refId":"comp_0","ind":3},{"ty":0,"nm":"all the layers","sr":1,"st":0,"op":60,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[256,256,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[256,256,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"w":512,"h":512,"refId":"comp_0","ind":4}],"v":"5.7.13","fr":60,"op":241,"ip":0,"assets":[{"nm":"all the layers","id":"comp_0","layers":[{"ty":4,"nm":"1 Outlines","sr":1,"st":0,"op":540,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[96,96,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.542,"y":0},"i":{"x":0.562,"y":1},"s":[175,208,0],"t":0,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.472,"y":0},"i":{"x":0.168,"y":0.858},"s":[175,277,0],"t":29,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.286,"y":0.063},"i":{"x":0.616,"y":0.711},"s":[175,172.812,0],"t":45,"ti":[0,0,0],"to":[0,0,0]},{"o":{"x":0.193,"y":1},"i":{"x":0.626,"y":1},"s":[175,213.122,0],"t":53,"ti":[0,0,0],"to":[0,0,0]},{"s":[175,208,0],"t":60}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,30.928],[30.928,0],[0,-30.928],[-30.928,0]],"o":[[0,-30.928],[-30.928,0],[0,30.928],[30.928,0]],"v":[[56,0],[0,-56],[-56,0],[0,56]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":10,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":16,"ix":5},"c":{"a":0,"k":[1,0.3098,0.6392],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[96,96],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}}],"ind":1},{"ty":4,"nm":"2 Outlines","sr":1,"st":0,"op":540,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[96,96,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[175,352,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[8.267,0],[0,0],[0,8.267],[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0]],"o":[[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0],[8.267,0],[0,0],[0,8.267]],"v":[[41.032,56],[-41.032,56],[-56,41.032],[-56,-41.032],[-41.032,-56],[41.032,-56],[56,-41.032],[56,41.032]]}],"t":0},{"o":{"x":0.167,"y":0.167},"i":{"x":0.667,"y":1},"s":[{"c":true,"i":[[8.267,0],[0,0],[0,8.267],[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0]],"o":[[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0],[8.267,0],[0,0],[0,8.267]],"v":[[41.032,56],[-41.032,56],[-56,41.032],[-56,-12.338],[-41.032,-27.306],[41.032,-27.306],[56,-12.338],[56,41.032]]}],"t":18},{"o":{"x":0.333,"y":0},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[8.267,0],[0,0],[0,8.267],[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0]],"o":[[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0],[8.267,0],[0,0],[0,8.267]],"v":[[41.032,56],[-41.032,56],[-56,41.032],[-56,11.468],[-41.032,-3.5],[41.032,-3.5],[56,11.468],[56,41.032]]}],"t":28},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[{"c":true,"i":[[8.267,0],[0,0],[0,8.267],[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0]],"o":[[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0],[8.267,0],[0,0],[0,8.267]],"v":[[41.032,56],[-41.032,56],[-56,41.032],[-55.999,-48.848],[-41.031,-63.816],[41.033,-63.816],[56.001,-48.848],[56,41.032]]}],"t":39},{"o":{"x":0.167,"y":0.167},"i":{"x":0.667,"y":1},"s":[{"c":true,"i":[[8.267,0],[0,0],[0,8.267],[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0]],"o":[[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0],[8.267,0],[0,0],[0,8.267]],"v":[[41.032,56],[-41.032,56],[-56,41.032],[-55.999,-32.655],[-41.031,-47.623],[41.033,-47.623],[56.001,-32.655],[56,41.032]]}],"t":50},{"s":[{"c":true,"i":[[8.267,0],[0,0],[0,8.267],[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0]],"o":[[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0],[8.267,0],[0,0],[0,8.267]],"v":[[41.032,56],[-41.032,56],[-56,41.032],[-56,-41.032],[-41.032,-56],[41.032,-56],[56,-41.032],[56,41.032]]}],"t":60}],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":10,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":16,"ix":5},"c":{"a":0,"k":[0.4118,0.7882,0.8588],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[96,96],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.4118,0.7882,0.8588],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}}],"ind":2},{"ty":4,"nm":"3 Outlines","sr":1,"st":0,"op":540,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[96,96,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[351,208,0],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.333,"y":0},"i":{"x":0,"y":1},"s":[0],"t":0},{"s":[360],"t":60}],"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[8.267,0],[0,0],[0,8.267],[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0]],"o":[[0,0],[-8.267,0],[0,0],[0,-8.267],[0,0],[8.267,0],[0,0],[0,8.267]],"v":[[41.032,56],[-41.032,56],[-56,41.032],[-56,-41.032],[-41.032,-56],[41.032,-56],[56,-41.032],[56,41.032]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 2","lc":1,"lj":1,"ml":10,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":16,"ix":5},"c":{"a":0,"k":[0.9647,0.898,0],"ix":3}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":10,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":16,"ix":5},"c":{"a":0,"k":[0.9647,0.898,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[96,96],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}}],"ind":3},{"ty":4,"nm":"4 Outlines","sr":1,"st":0,"op":540,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[96,106.629,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[351,362.371,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":1,"y":0},"i":{"x":0.667,"y":1},"s":[{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[56,56.129],[-56,56.129],[0,-56.129]]}],"t":0},{"o":{"x":0.333,"y":0},"i":{"x":0,"y":1},"s":[{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[56,56.129],[-56,56.129],[0,-7.629]]}],"t":29},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[56,56.129],[-56,56.129],[0,-62.629]]}],"t":39},{"o":{"x":0.333,"y":0},"i":{"x":0.667,"y":1},"s":[{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[56,56.129],[-56,56.129],[0,-48.129]]}],"t":50},{"s":[{"c":true,"i":[[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0]],"v":[[56,56.129],[-56,56.129],[0,-56.129]]}],"t":60}],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":2,"lj":2,"ml":1,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":16,"ix":5},"c":{"a":0,"k":[1,0.3098,0.6392],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[96,96.129],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}}],"ind":4}]}]}';

function instance$6($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_paragraph_1 } = $$props;
	let { action_button } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_paragraph_1' in $$props) $$invalidate(1, content_paragraph_1 = $$props.content_paragraph_1);
		if ('action_button' in $$props) $$invalidate(2, action_button = $$props.action_button);
	};

	return [content_title, content_paragraph_1, action_button, favicon];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
			favicon: 3,
			content_title: 0,
			content_paragraph_1: 1,
			action_button: 2
		});
	}
}

var commonjsGlobal = typeof globalThis !== "undefined" ? globalThis : typeof window !== "undefined" ? window : typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : {};
function getDefaultExportFromCjs(x) {
  return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, "default") ? x["default"] : x;
}
function createCommonjsModule(fn, basedir, module) {
  return module = {
    path: basedir,
    exports: {},
    require: function(path, base) {
      return commonjsRequire(path, base === void 0 || base === null ? module.path : base);
    }
  }, fn(module, module.exports), module.exports;
}
function commonjsRequire() {
  throw new Error("Dynamic requires are not currently supported by @rollup/plugin-commonjs");
}
var siema_min = createCommonjsModule(function(module, exports) {
  !function(e, t) {
    module.exports = t();
  }(typeof self != "undefined" ? self : commonjsGlobal, function() {
    return function(e) {
      function t(r) {
        if (i[r])
          return i[r].exports;
        var n = i[r] = {i: r, l: false, exports: {}};
        return e[r].call(n.exports, n, n.exports, t), n.l = true, n.exports;
      }
      var i = {};
      return t.m = e, t.c = i, t.d = function(e2, i2, r) {
        t.o(e2, i2) || Object.defineProperty(e2, i2, {configurable: false, enumerable: true, get: r});
      }, t.n = function(e2) {
        var i2 = e2 && e2.__esModule ? function() {
          return e2.default;
        } : function() {
          return e2;
        };
        return t.d(i2, "a", i2), i2;
      }, t.o = function(e2, t2) {
        return Object.prototype.hasOwnProperty.call(e2, t2);
      }, t.p = "", t(t.s = 0);
    }([function(e, t, i) {
      function r(e2, t2) {
        if (!(e2 instanceof t2))
          throw new TypeError("Cannot call a class as a function");
      }
      Object.defineProperty(t, "__esModule", {value: true});
      var n = typeof Symbol == "function" && typeof Symbol.iterator == "symbol" ? function(e2) {
        return typeof e2;
      } : function(e2) {
        return e2 && typeof Symbol == "function" && e2.constructor === Symbol && e2 !== Symbol.prototype ? "symbol" : typeof e2;
      }, s = function() {
        function e2(e3, t2) {
          for (var i2 = 0; i2 < t2.length; i2++) {
            var r2 = t2[i2];
            r2.enumerable = r2.enumerable || false, r2.configurable = true, "value" in r2 && (r2.writable = true), Object.defineProperty(e3, r2.key, r2);
          }
        }
        return function(t2, i2, r2) {
          return i2 && e2(t2.prototype, i2), r2 && e2(t2, r2), t2;
        };
      }(), l = function() {
        function e2(t2) {
          var i2 = this;
          if (r(this, e2), this.config = e2.mergeSettings(t2), this.selector = typeof this.config.selector == "string" ? document.querySelector(this.config.selector) : this.config.selector, this.selector === null)
            throw new Error("Something wrong with your selector \u{1F62D}");
          this.resolveSlidesNumber(), this.selectorWidth = this.selector.offsetWidth, this.innerElements = [].slice.call(this.selector.children), this.currentSlide = this.config.loop ? this.config.startIndex % this.innerElements.length : Math.max(0, Math.min(this.config.startIndex, this.innerElements.length - this.perPage)), this.transformProperty = e2.webkitOrNot(), ["resizeHandler", "touchstartHandler", "touchendHandler", "touchmoveHandler", "mousedownHandler", "mouseupHandler", "mouseleaveHandler", "mousemoveHandler", "clickHandler"].forEach(function(e3) {
            i2[e3] = i2[e3].bind(i2);
          }), this.init();
        }
        return s(e2, [{key: "attachEvents", value: function() {
          window.addEventListener("resize", this.resizeHandler), this.config.draggable && (this.pointerDown = false, this.drag = {startX: 0, endX: 0, startY: 0, letItGo: null, preventClick: false}, this.selector.addEventListener("touchstart", this.touchstartHandler), this.selector.addEventListener("touchend", this.touchendHandler), this.selector.addEventListener("touchmove", this.touchmoveHandler), this.selector.addEventListener("mousedown", this.mousedownHandler), this.selector.addEventListener("mouseup", this.mouseupHandler), this.selector.addEventListener("mouseleave", this.mouseleaveHandler), this.selector.addEventListener("mousemove", this.mousemoveHandler), this.selector.addEventListener("click", this.clickHandler));
        }}, {key: "detachEvents", value: function() {
          window.removeEventListener("resize", this.resizeHandler), this.selector.removeEventListener("touchstart", this.touchstartHandler), this.selector.removeEventListener("touchend", this.touchendHandler), this.selector.removeEventListener("touchmove", this.touchmoveHandler), this.selector.removeEventListener("mousedown", this.mousedownHandler), this.selector.removeEventListener("mouseup", this.mouseupHandler), this.selector.removeEventListener("mouseleave", this.mouseleaveHandler), this.selector.removeEventListener("mousemove", this.mousemoveHandler), this.selector.removeEventListener("click", this.clickHandler);
        }}, {key: "init", value: function() {
          this.attachEvents(), this.selector.style.overflow = "hidden", this.selector.style.direction = this.config.rtl ? "rtl" : "ltr", this.buildSliderFrame(), this.config.onInit.call(this);
        }}, {key: "buildSliderFrame", value: function() {
          var e3 = this.selectorWidth / this.perPage, t2 = this.config.loop ? this.innerElements.length + 2 * this.perPage : this.innerElements.length;
          this.sliderFrame = document.createElement("div"), this.sliderFrame.style.width = e3 * t2 + "px", this.enableTransition(), this.config.draggable && (this.selector.style.cursor = "-webkit-grab");
          var i2 = document.createDocumentFragment();
          if (this.config.loop)
            for (var r2 = this.innerElements.length - this.perPage; r2 < this.innerElements.length; r2++) {
              var n2 = this.buildSliderFrameItem(this.innerElements[r2].cloneNode(true));
              i2.appendChild(n2);
            }
          for (var s2 = 0; s2 < this.innerElements.length; s2++) {
            var l2 = this.buildSliderFrameItem(this.innerElements[s2]);
            i2.appendChild(l2);
          }
          if (this.config.loop)
            for (var o = 0; o < this.perPage; o++) {
              var a = this.buildSliderFrameItem(this.innerElements[o].cloneNode(true));
              i2.appendChild(a);
            }
          this.sliderFrame.appendChild(i2), this.selector.innerHTML = "", this.selector.appendChild(this.sliderFrame), this.slideToCurrent();
        }}, {key: "buildSliderFrameItem", value: function(e3) {
          var t2 = document.createElement("div");
          return t2.style.cssFloat = this.config.rtl ? "right" : "left", t2.style.float = this.config.rtl ? "right" : "left", t2.style.width = (this.config.loop ? 100 / (this.innerElements.length + 2 * this.perPage) : 100 / this.innerElements.length) + "%", t2.appendChild(e3), t2;
        }}, {key: "resolveSlidesNumber", value: function() {
          if (typeof this.config.perPage == "number")
            this.perPage = this.config.perPage;
          else if (n(this.config.perPage) === "object") {
            this.perPage = 1;
            for (var e3 in this.config.perPage)
              window.innerWidth >= e3 && (this.perPage = this.config.perPage[e3]);
          }
        }}, {key: "prev", value: function() {
          var e3 = arguments.length > 0 && arguments[0] !== void 0 ? arguments[0] : 1, t2 = arguments[1];
          if (!(this.innerElements.length <= this.perPage)) {
            var i2 = this.currentSlide;
            if (this.config.loop) {
              if (this.currentSlide - e3 < 0) {
                this.disableTransition();
                var r2 = this.currentSlide + this.innerElements.length, n2 = this.perPage, s2 = r2 + n2, l2 = (this.config.rtl ? 1 : -1) * s2 * (this.selectorWidth / this.perPage), o = this.config.draggable ? this.drag.endX - this.drag.startX : 0;
                this.sliderFrame.style[this.transformProperty] = "translate3d(" + (l2 + o) + "px, 0, 0)", this.currentSlide = r2 - e3;
              } else
                this.currentSlide = this.currentSlide - e3;
            } else
              this.currentSlide = Math.max(this.currentSlide - e3, 0);
            i2 !== this.currentSlide && (this.slideToCurrent(this.config.loop), this.config.onChange.call(this), t2 && t2.call(this));
          }
        }}, {key: "next", value: function() {
          var e3 = arguments.length > 0 && arguments[0] !== void 0 ? arguments[0] : 1, t2 = arguments[1];
          if (!(this.innerElements.length <= this.perPage)) {
            var i2 = this.currentSlide;
            if (this.config.loop) {
              if (this.currentSlide + e3 > this.innerElements.length - this.perPage) {
                this.disableTransition();
                var r2 = this.currentSlide - this.innerElements.length, n2 = this.perPage, s2 = r2 + n2, l2 = (this.config.rtl ? 1 : -1) * s2 * (this.selectorWidth / this.perPage), o = this.config.draggable ? this.drag.endX - this.drag.startX : 0;
                this.sliderFrame.style[this.transformProperty] = "translate3d(" + (l2 + o) + "px, 0, 0)", this.currentSlide = r2 + e3;
              } else
                this.currentSlide = this.currentSlide + e3;
            } else
              this.currentSlide = Math.min(this.currentSlide + e3, this.innerElements.length - this.perPage);
            i2 !== this.currentSlide && (this.slideToCurrent(this.config.loop), this.config.onChange.call(this), t2 && t2.call(this));
          }
        }}, {key: "disableTransition", value: function() {
          this.sliderFrame.style.webkitTransition = "all 0ms " + this.config.easing, this.sliderFrame.style.transition = "all 0ms " + this.config.easing;
        }}, {key: "enableTransition", value: function() {
          this.sliderFrame.style.webkitTransition = "all " + this.config.duration + "ms " + this.config.easing, this.sliderFrame.style.transition = "all " + this.config.duration + "ms " + this.config.easing;
        }}, {key: "goTo", value: function(e3, t2) {
          if (!(this.innerElements.length <= this.perPage)) {
            var i2 = this.currentSlide;
            this.currentSlide = this.config.loop ? e3 % this.innerElements.length : Math.min(Math.max(e3, 0), this.innerElements.length - this.perPage), i2 !== this.currentSlide && (this.slideToCurrent(), this.config.onChange.call(this), t2 && t2.call(this));
          }
        }}, {key: "slideToCurrent", value: function(e3) {
          var t2 = this, i2 = this.config.loop ? this.currentSlide + this.perPage : this.currentSlide, r2 = (this.config.rtl ? 1 : -1) * i2 * (this.selectorWidth / this.perPage);
          e3 ? requestAnimationFrame(function() {
            requestAnimationFrame(function() {
              t2.enableTransition(), t2.sliderFrame.style[t2.transformProperty] = "translate3d(" + r2 + "px, 0, 0)";
            });
          }) : this.sliderFrame.style[this.transformProperty] = "translate3d(" + r2 + "px, 0, 0)";
        }}, {key: "updateAfterDrag", value: function() {
          var e3 = (this.config.rtl ? -1 : 1) * (this.drag.endX - this.drag.startX), t2 = Math.abs(e3), i2 = this.config.multipleDrag ? Math.ceil(t2 / (this.selectorWidth / this.perPage)) : 1, r2 = e3 > 0 && this.currentSlide - i2 < 0, n2 = e3 < 0 && this.currentSlide + i2 > this.innerElements.length - this.perPage;
          e3 > 0 && t2 > this.config.threshold && this.innerElements.length > this.perPage ? this.prev(i2) : e3 < 0 && t2 > this.config.threshold && this.innerElements.length > this.perPage && this.next(i2), this.slideToCurrent(r2 || n2);
        }}, {key: "resizeHandler", value: function() {
          this.resolveSlidesNumber(), this.currentSlide + this.perPage > this.innerElements.length && (this.currentSlide = this.innerElements.length <= this.perPage ? 0 : this.innerElements.length - this.perPage), this.selectorWidth = this.selector.offsetWidth, this.buildSliderFrame();
        }}, {key: "clearDrag", value: function() {
          this.drag = {startX: 0, endX: 0, startY: 0, letItGo: null, preventClick: this.drag.preventClick};
        }}, {key: "touchstartHandler", value: function(e3) {
          ["TEXTAREA", "OPTION", "INPUT", "SELECT"].indexOf(e3.target.nodeName) !== -1 || (e3.stopPropagation(), this.pointerDown = true, this.drag.startX = e3.touches[0].pageX, this.drag.startY = e3.touches[0].pageY);
        }}, {key: "touchendHandler", value: function(e3) {
          e3.stopPropagation(), this.pointerDown = false, this.enableTransition(), this.drag.endX && this.updateAfterDrag(), this.clearDrag();
        }}, {key: "touchmoveHandler", value: function(e3) {
          if (e3.stopPropagation(), this.drag.letItGo === null && (this.drag.letItGo = Math.abs(this.drag.startY - e3.touches[0].pageY) < Math.abs(this.drag.startX - e3.touches[0].pageX)), this.pointerDown && this.drag.letItGo) {
            e3.preventDefault(), this.drag.endX = e3.touches[0].pageX, this.sliderFrame.style.webkitTransition = "all 0ms " + this.config.easing, this.sliderFrame.style.transition = "all 0ms " + this.config.easing;
            var t2 = this.config.loop ? this.currentSlide + this.perPage : this.currentSlide, i2 = t2 * (this.selectorWidth / this.perPage), r2 = this.drag.endX - this.drag.startX, n2 = this.config.rtl ? i2 + r2 : i2 - r2;
            this.sliderFrame.style[this.transformProperty] = "translate3d(" + (this.config.rtl ? 1 : -1) * n2 + "px, 0, 0)";
          }
        }}, {key: "mousedownHandler", value: function(e3) {
          ["TEXTAREA", "OPTION", "INPUT", "SELECT"].indexOf(e3.target.nodeName) !== -1 || (e3.preventDefault(), e3.stopPropagation(), this.pointerDown = true, this.drag.startX = e3.pageX);
        }}, {key: "mouseupHandler", value: function(e3) {
          e3.stopPropagation(), this.pointerDown = false, this.selector.style.cursor = "-webkit-grab", this.enableTransition(), this.drag.endX && this.updateAfterDrag(), this.clearDrag();
        }}, {key: "mousemoveHandler", value: function(e3) {
          if (e3.preventDefault(), this.pointerDown) {
            e3.target.nodeName === "A" && (this.drag.preventClick = true), this.drag.endX = e3.pageX, this.selector.style.cursor = "-webkit-grabbing", this.sliderFrame.style.webkitTransition = "all 0ms " + this.config.easing, this.sliderFrame.style.transition = "all 0ms " + this.config.easing;
            var t2 = this.config.loop ? this.currentSlide + this.perPage : this.currentSlide, i2 = t2 * (this.selectorWidth / this.perPage), r2 = this.drag.endX - this.drag.startX, n2 = this.config.rtl ? i2 + r2 : i2 - r2;
            this.sliderFrame.style[this.transformProperty] = "translate3d(" + (this.config.rtl ? 1 : -1) * n2 + "px, 0, 0)";
          }
        }}, {key: "mouseleaveHandler", value: function(e3) {
          this.pointerDown && (this.pointerDown = false, this.selector.style.cursor = "-webkit-grab", this.drag.endX = e3.pageX, this.drag.preventClick = false, this.enableTransition(), this.updateAfterDrag(), this.clearDrag());
        }}, {key: "clickHandler", value: function(e3) {
          this.drag.preventClick && e3.preventDefault(), this.drag.preventClick = false;
        }}, {key: "remove", value: function(e3, t2) {
          if (e3 < 0 || e3 >= this.innerElements.length)
            throw new Error("Item to remove doesn't exist \u{1F62D}");
          var i2 = e3 < this.currentSlide, r2 = this.currentSlide + this.perPage - 1 === e3;
          (i2 || r2) && this.currentSlide--, this.innerElements.splice(e3, 1), this.buildSliderFrame(), t2 && t2.call(this);
        }}, {key: "insert", value: function(e3, t2, i2) {
          if (t2 < 0 || t2 > this.innerElements.length + 1)
            throw new Error("Unable to inset it at this index \u{1F62D}");
          if (this.innerElements.indexOf(e3) !== -1)
            throw new Error("The same item in a carousel? Really? Nope \u{1F62D}");
          var r2 = t2 <= this.currentSlide > 0 && this.innerElements.length;
          this.currentSlide = r2 ? this.currentSlide + 1 : this.currentSlide, this.innerElements.splice(t2, 0, e3), this.buildSliderFrame(), i2 && i2.call(this);
        }}, {key: "prepend", value: function(e3, t2) {
          this.insert(e3, 0), t2 && t2.call(this);
        }}, {key: "append", value: function(e3, t2) {
          this.insert(e3, this.innerElements.length + 1), t2 && t2.call(this);
        }}, {key: "destroy", value: function() {
          var e3 = arguments.length > 0 && arguments[0] !== void 0 && arguments[0], t2 = arguments[1];
          if (this.detachEvents(), this.selector.style.cursor = "auto", e3) {
            for (var i2 = document.createDocumentFragment(), r2 = 0; r2 < this.innerElements.length; r2++)
              i2.appendChild(this.innerElements[r2]);
            this.selector.innerHTML = "", this.selector.appendChild(i2), this.selector.removeAttribute("style");
          }
          t2 && t2.call(this);
        }}], [{key: "mergeSettings", value: function(e3) {
          var t2 = {selector: ".siema", duration: 200, easing: "ease-out", perPage: 1, startIndex: 0, draggable: true, multipleDrag: true, threshold: 20, loop: false, rtl: false, onInit: function() {
          }, onChange: function() {
          }}, i2 = e3;
          for (var r2 in i2)
            t2[r2] = i2[r2];
          return t2;
        }}, {key: "webkitOrNot", value: function() {
          return typeof document.documentElement.style.transform == "string" ? "transform" : "WebkitTransform";
        }}]), e2;
      }();
      t.default = l, e.exports = t.default;
    }]);
  });
});
var __pika_web_default_export_for_treeshaking__ = /* @__PURE__ */ getDefaultExportFromCjs(siema_min);
var Siema = siema_min.Siema;

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[14] = list[i];
	child_ctx[16] = i;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[17] = list[i];
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[17] = list[i];
	return child_ctx;
}

// (344:8) {#if content_tag}
function create_if_block$2(ctx) {
	let div;
	let h6;
	let t;

	return {
		c() {
			div = element("div");
			h6 = element("h6");
			t = text(/*content_tag*/ ctx[0]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			h6 = claim_element(div_nodes, "H6", {});
			var h6_nodes = children(h6);
			t = claim_text(h6_nodes, /*content_tag*/ ctx[0]);
			h6_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "tag-pink-large svelte-1m7fkq");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, h6);
			append_hydration(h6, t);
		},
		p(ctx, dirty) {
			if (dirty & /*content_tag*/ 1) set_data(t, /*content_tag*/ ctx[0]);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (356:10) {#each content_card as card}
function create_each_block_2(ctx) {
	let div2;
	let div0;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let h6;
	let t1_value = /*card*/ ctx[17].title + "";
	let t1;
	let t2;
	let div1;
	let p;
	let t3_value = /*card*/ ctx[17].description + "";
	let t3;
	let t4;

	return {
		c() {
			div2 = element("div");
			div0 = element("div");
			img = element("img");
			t0 = space();
			h6 = element("h6");
			t1 = text(t1_value);
			t2 = space();
			div1 = element("div");
			p = element("p");
			t3 = text(t3_value);
			t4 = space();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			img = claim_element(div0_nodes, "IMG", { src: true, alt: true, class: true });
			t0 = claim_space(div0_nodes);
			h6 = claim_element(div0_nodes, "H6", {});
			var h6_nodes = children(h6);
			t1 = claim_text(h6_nodes, t1_value);
			h6_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t2 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			p = claim_element(div1_nodes, "P", { class: true });
			var p_nodes = children(p);
			t3 = claim_text(p_nodes, t3_value);
			p_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*card*/ ctx[17].image.alt);
			attr(img, "class", "svelte-1m7fkq");
			attr(div0, "class", "card-title-wrapper svelte-1m7fkq");
			attr(p, "class", "p-medium");
			attr(div1, "class", "card-content-wrapper svelte-1m7fkq");
			attr(div2, "class", "card-wrapper slider svelte-1m7fkq");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div0);
			append_hydration(div0, img);
			append_hydration(div0, t0);
			append_hydration(div0, h6);
			append_hydration(h6, t1);
			append_hydration(div2, t2);
			append_hydration(div2, div1);
			append_hydration(div1, p);
			append_hydration(p, t3);
			append_hydration(div2, t4);
		},
		p(ctx, dirty) {
			if (dirty & /*content_card*/ 8 && !src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*content_card*/ 8 && img_alt_value !== (img_alt_value = /*card*/ ctx[17].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*content_card*/ 8 && t1_value !== (t1_value = /*card*/ ctx[17].title + "")) set_data(t1, t1_value);
			if (dirty & /*content_card*/ 8 && t3_value !== (t3_value = /*card*/ ctx[17].description + "")) set_data(t3, t3_value);
		},
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

// (371:8) {#each content_card as card}
function create_each_block_1$1(ctx) {
	let div2;
	let div0;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let h6;
	let t1_value = /*card*/ ctx[17].title + "";
	let t1;
	let t2;
	let div1;
	let p;
	let t3_value = /*card*/ ctx[17].description + "";
	let t3;
	let t4;

	return {
		c() {
			div2 = element("div");
			div0 = element("div");
			img = element("img");
			t0 = space();
			h6 = element("h6");
			t1 = text(t1_value);
			t2 = space();
			div1 = element("div");
			p = element("p");
			t3 = text(t3_value);
			t4 = space();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			img = claim_element(div0_nodes, "IMG", { src: true, alt: true, class: true });
			t0 = claim_space(div0_nodes);
			h6 = claim_element(div0_nodes, "H6", {});
			var h6_nodes = children(h6);
			t1 = claim_text(h6_nodes, t1_value);
			h6_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t2 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			p = claim_element(div1_nodes, "P", { class: true });
			var p_nodes = children(p);
			t3 = claim_text(p_nodes, t3_value);
			p_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*card*/ ctx[17].image.alt);
			attr(img, "class", "svelte-1m7fkq");
			attr(div0, "class", "card-title-wrapper svelte-1m7fkq");
			attr(p, "class", "p-medium");
			attr(div1, "class", "card-content-wrapper svelte-1m7fkq");
			attr(div2, "class", "card-wrapper slider svelte-1m7fkq");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div0);
			append_hydration(div0, img);
			append_hydration(div0, t0);
			append_hydration(div0, h6);
			append_hydration(h6, t1);
			append_hydration(div2, t2);
			append_hydration(div2, div1);
			append_hydration(div1, p);
			append_hydration(p, t3);
			append_hydration(div2, t4);
		},
		p(ctx, dirty) {
			if (dirty & /*content_card*/ 8 && !src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*content_card*/ 8 && img_alt_value !== (img_alt_value = /*card*/ ctx[17].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*content_card*/ 8 && t1_value !== (t1_value = /*card*/ ctx[17].title + "")) set_data(t1, t1_value);
			if (dirty & /*content_card*/ 8 && t3_value !== (t3_value = /*card*/ ctx[17].description + "")) set_data(t3, t3_value);
		},
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

// (388:6) {#each data as d, i}
function create_each_block$2(ctx) {
	let input;
	let input_id_value;
	let input_value_value;
	let input_checked_value;
	let mounted;
	let dispose;

	function click_handler() {
		return /*click_handler*/ ctx[10](/*i*/ ctx[16]);
	}

	return {
		c() {
			input = element("input");
			this.h();
		},
		l(nodes) {
			input = claim_element(nodes, "INPUT", {
				type: true,
				"aria-label": true,
				id: true,
				name: true,
				class: true
			});

			this.h();
		},
		h() {
			attr(input, "type", "radio");
			attr(input, "aria-label", "bullet");
			attr(input, "id", input_id_value = /*i*/ ctx[16]);
			attr(input, "name", "slider-radio");
			input.value = input_value_value = /*i*/ ctx[16];
			input.checked = input_checked_value = /*select*/ ctx[6] == /*i*/ ctx[16];
			attr(input, "class", "svelte-1m7fkq");
		},
		m(target, anchor) {
			insert_hydration(target, input, anchor);
			/*input_binding*/ ctx[9](input);

			if (!mounted) {
				dispose = listen(input, "click", click_handler);
				mounted = true;
			}
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;

			if (dirty & /*select*/ 64 && input_checked_value !== (input_checked_value = /*select*/ ctx[6] == /*i*/ ctx[16])) {
				input.checked = input_checked_value;
			}
		},
		d(detaching) {
			if (detaching) detach(input);
			/*input_binding*/ ctx[9](null);
			mounted = false;
			dispose();
		}
	};
}

function create_fragment$7(ctx) {
	let div9;
	let div8;
	let div7;
	let div3;
	let div1;
	let t0;
	let div0;
	let h3;
	let t1;
	let t2;
	let p;
	let t3;
	let t4;
	let div2;
	let t5;
	let div5;
	let div4;
	let t6;
	let div6;
	let if_block = /*content_tag*/ ctx[0] && create_if_block$2(ctx);
	let each_value_2 = /*content_card*/ ctx[3];
	let each_blocks_2 = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks_2[i] = create_each_block_2(get_each_context_2(ctx, each_value_2, i));
	}

	let each_value_1 = /*content_card*/ ctx[3];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	let each_value = /*data*/ ctx[7];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	return {
		c() {
			div9 = element("div");
			div8 = element("div");
			div7 = element("div");
			div3 = element("div");
			div1 = element("div");
			if (if_block) if_block.c();
			t0 = space();
			div0 = element("div");
			h3 = element("h3");
			t1 = text(/*content_title*/ ctx[1]);
			t2 = space();
			p = element("p");
			t3 = text(/*content_paragraph_1*/ ctx[2]);
			t4 = space();
			div2 = element("div");

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				each_blocks_2[i].c();
			}

			t5 = space();
			div5 = element("div");
			div4 = element("div");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t6 = space();
			div6 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div9 = claim_element(nodes, "DIV", { class: true, id: true });
			var div9_nodes = children(div9);
			div8 = claim_element(div9_nodes, "DIV", { class: true });
			var div8_nodes = children(div8);
			div7 = claim_element(div8_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			div3 = claim_element(div7_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			if (if_block) if_block.l(div1_nodes);
			t0 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h3 = claim_element(div0_nodes, "H3", {});
			var h3_nodes = children(h3);
			t1 = claim_text(h3_nodes, /*content_title*/ ctx[1]);
			h3_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			p = claim_element(div0_nodes, "P", { class: true });
			var p_nodes = children(p);
			t3 = claim_text(p_nodes, /*content_paragraph_1*/ ctx[2]);
			p_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t4 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				each_blocks_2[i].l(div2_nodes);
			}

			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t5 = claim_space(div7_nodes);
			div5 = claim_element(div7_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(div4_nodes);
			}

			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			t6 = claim_space(div7_nodes);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div6_nodes);
			}

			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			div9_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p, "class", "p-large");
			attr(div0, "class", "section-container content svelte-1m7fkq");
			attr(div1, "class", "content-header-wrapper svelte-1m7fkq");
			attr(div2, "class", "card-container-desktop svelte-1m7fkq");
			attr(div3, "class", "content-wrapper svelte-1m7fkq");
			attr(div4, "class", "siema svelte-1m7fkq");
			attr(div5, "class", "card-container-mobile svelte-1m7fkq");
			attr(div6, "class", "bullet svelte-1m7fkq");
			attr(div7, "class", "wrapper svelte-1m7fkq");
			attr(div8, "class", "container svelte-1m7fkq");
			attr(div9, "class", "section");
			attr(div9, "id", "section-c9f6d913");
		},
		m(target, anchor) {
			insert_hydration(target, div9, anchor);
			append_hydration(div9, div8);
			append_hydration(div8, div7);
			append_hydration(div7, div3);
			append_hydration(div3, div1);
			if (if_block) if_block.m(div1, null);
			append_hydration(div1, t0);
			append_hydration(div1, div0);
			append_hydration(div0, h3);
			append_hydration(h3, t1);
			append_hydration(div0, t2);
			append_hydration(div0, p);
			append_hydration(p, t3);
			append_hydration(div3, t4);
			append_hydration(div3, div2);

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				if (each_blocks_2[i]) {
					each_blocks_2[i].m(div2, null);
				}
			}

			append_hydration(div7, t5);
			append_hydration(div7, div5);
			append_hydration(div5, div4);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(div4, null);
				}
			}

			append_hydration(div7, t6);
			append_hydration(div7, div6);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div6, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (/*content_tag*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$2(ctx);
					if_block.c();
					if_block.m(div1, t0);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*content_title*/ 2) set_data(t1, /*content_title*/ ctx[1]);
			if (dirty & /*content_paragraph_1*/ 4) set_data(t3, /*content_paragraph_1*/ ctx[2]);

			if (dirty & /*content_card*/ 8) {
				each_value_2 = /*content_card*/ ctx[3];
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2(ctx, each_value_2, i);

					if (each_blocks_2[i]) {
						each_blocks_2[i].p(child_ctx, dirty);
					} else {
						each_blocks_2[i] = create_each_block_2(child_ctx);
						each_blocks_2[i].c();
						each_blocks_2[i].m(div2, null);
					}
				}

				for (; i < each_blocks_2.length; i += 1) {
					each_blocks_2[i].d(1);
				}

				each_blocks_2.length = each_value_2.length;
			}

			if (dirty & /*content_card*/ 8) {
				each_value_1 = /*content_card*/ ctx[3];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1$1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(div4, null);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty & /*select, radioSlider, slider*/ 112) {
				each_value = /*data*/ ctx[7];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div6, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div9);
			if (if_block) if_block.d();
			destroy_each(each_blocks_2, detaching);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_tag } = $$props;
	let { content_title } = $$props;
	let { content_paragraph_1 } = $$props;
	let { content_card } = $$props;
	let slider, radioSlider;
	let select = 0;
	let data = [{ val: 1 }, { val: 2 }, { val: 3 }, { val: 4 }, { val: 5 }];

	function updateSlideIndex() {
		if (this.currentSlide === -1) {
			$$invalidate(6, select = 4);
			return;
		}

		$$invalidate(6, select = this.currentSlide);
	}

	onMount(() => {
		$$invalidate(4, slider = new __pika_web_default_export_for_treeshaking__({
				selector: '.siema',
				duration: 200,
				easing: 'ease-in-out',
				perPage: {
					0: 1, // 2 items for viewport wider than 800px
					540: 2,
					865: 3, // 3 items for viewport wider than 1240px
					1020: 4
				},
				startIndex: 0,
				draggable: true,
				multipleDrag: true,
				threshold: 20,
				loop: false,
				rtl: false,
				onInit: () => {
					
				},
				onChange: updateSlideIndex
			})); // onChange: (e) => console.log("e"),
		//end Siema constructor
	}); // prev = () => {
	//     slider.prev()
	//     if (select > 0) {
	//         select--

	function input_binding($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			radioSlider = $$value;
			$$invalidate(5, radioSlider);
		});
	}

	const click_handler = i => {
		slider.goTo(i);
	};

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(8, favicon = $$props.favicon);
		if ('content_tag' in $$props) $$invalidate(0, content_tag = $$props.content_tag);
		if ('content_title' in $$props) $$invalidate(1, content_title = $$props.content_title);
		if ('content_paragraph_1' in $$props) $$invalidate(2, content_paragraph_1 = $$props.content_paragraph_1);
		if ('content_card' in $$props) $$invalidate(3, content_card = $$props.content_card);
	};

	return [
		content_tag,
		content_title,
		content_paragraph_1,
		content_card,
		slider,
		radioSlider,
		select,
		data,
		favicon,
		input_binding,
		click_handler
	];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			favicon: 8,
			content_tag: 0,
			content_title: 1,
			content_paragraph_1: 2,
			content_card: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$8(ctx) {
	let div16;
	let div15;
	let div14;
	let div5;
	let div3;
	let div0;
	let h60;
	let t0;
	let t1;
	let h40;
	let t2;
	let t3;
	let p0;
	let t4;
	let t5;
	let p1;
	let t6;
	let t7;
	let div1;
	let lottie_player0;
	let lottie_player0_src_value;
	let t8;
	let img0;
	let img0_src_value;
	let img0_alt_value;
	let t9;
	let div2;
	let a0;
	let t10_value = /*content_action_1*/ ctx[5].label + "";
	let t10;
	let a0_href_value;
	let t11;
	let div4;
	let lottie_player1;
	let lottie_player1_src_value;
	let t12;
	let img1;
	let img1_src_value;
	let img1_alt_value;
	let t13;
	let div13;
	let div6;
	let lottie_player2;
	let lottie_player2_src_value;
	let t14;
	let img2;
	let img2_src_value;
	let img2_alt_value;
	let t15;
	let div12;
	let div7;
	let h61;
	let t16;
	let t17;
	let h41;
	let t18;
	let t19;
	let p2;
	let t20;
	let t21;
	let div8;
	let img3;
	let img3_src_value;
	let img3_alt_value;
	let t22;
	let p3;
	let t23;
	let t24;
	let div9;
	let img4;
	let img4_src_value;
	let img4_alt_value;
	let t25;
	let p4;
	let t26;
	let t27;
	let p5;
	let t28;
	let t29;
	let div10;
	let lottie_player3;
	let lottie_player3_src_value;
	let t30;
	let img5;
	let img5_src_value;
	let img5_alt_value;
	let t31;
	let div11;
	let a1;
	let t32_value = /*content_action_2*/ ctx[13].label + "";
	let t32;
	let a1_href_value;

	return {
		c() {
			div16 = element("div");
			div15 = element("div");
			div14 = element("div");
			div5 = element("div");
			div3 = element("div");
			div0 = element("div");
			h60 = element("h6");
			t0 = text(/*content_tag_1*/ ctx[0]);
			t1 = space();
			h40 = element("h4");
			t2 = text(/*content_title_1*/ ctx[1]);
			t3 = space();
			p0 = element("p");
			t4 = text(/*content_description_1a*/ ctx[2]);
			t5 = space();
			p1 = element("p");
			t6 = text(/*content_description_1b*/ ctx[3]);
			t7 = space();
			div1 = element("div");
			lottie_player0 = element("lottie-player");
			t8 = space();
			img0 = element("img");
			t9 = space();
			div2 = element("div");
			a0 = element("a");
			t10 = text(t10_value);
			t11 = space();
			div4 = element("div");
			lottie_player1 = element("lottie-player");
			t12 = space();
			img1 = element("img");
			t13 = space();
			div13 = element("div");
			div6 = element("div");
			lottie_player2 = element("lottie-player");
			t14 = space();
			img2 = element("img");
			t15 = space();
			div12 = element("div");
			div7 = element("div");
			h61 = element("h6");
			t16 = text(/*content_tag_2*/ ctx[6]);
			t17 = space();
			h41 = element("h4");
			t18 = text(/*content_title_2*/ ctx[7]);
			t19 = space();
			p2 = element("p");
			t20 = text(/*content_description_2a*/ ctx[8]);
			t21 = space();
			div8 = element("div");
			img3 = element("img");
			t22 = space();
			p3 = element("p");
			t23 = text(/*content_description_2b*/ ctx[9]);
			t24 = space();
			div9 = element("div");
			img4 = element("img");
			t25 = space();
			p4 = element("p");
			t26 = text(/*content_description_2c*/ ctx[10]);
			t27 = space();
			p5 = element("p");
			t28 = text(/*content_description_2d*/ ctx[11]);
			t29 = space();
			div10 = element("div");
			lottie_player3 = element("lottie-player");
			t30 = space();
			img5 = element("img");
			t31 = space();
			div11 = element("div");
			a1 = element("a");
			t32 = text(t32_value);
			this.h();
		},
		l(nodes) {
			div16 = claim_element(nodes, "DIV", { class: true, id: true });
			var div16_nodes = children(div16);
			div15 = claim_element(div16_nodes, "DIV", { class: true });
			var div15_nodes = children(div15);
			div14 = claim_element(div15_nodes, "DIV", { class: true });
			var div14_nodes = children(div14);
			div5 = claim_element(div14_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div3 = claim_element(div5_nodes, "DIV", {});
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h60 = claim_element(div0_nodes, "H6", {});
			var h60_nodes = children(h60);
			t0 = claim_text(h60_nodes, /*content_tag_1*/ ctx[0]);
			h60_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div3_nodes);
			h40 = claim_element(div3_nodes, "H4", {});
			var h40_nodes = children(h40);
			t2 = claim_text(h40_nodes, /*content_title_1*/ ctx[1]);
			h40_nodes.forEach(detach);
			t3 = claim_space(div3_nodes);
			p0 = claim_element(div3_nodes, "P", { class: true });
			var p0_nodes = children(p0);
			t4 = claim_text(p0_nodes, /*content_description_1a*/ ctx[2]);
			p0_nodes.forEach(detach);
			t5 = claim_space(div3_nodes);
			p1 = claim_element(div3_nodes, "P", { class: true });
			var p1_nodes = children(p1);
			t6 = claim_text(p1_nodes, /*content_description_1b*/ ctx[3]);
			p1_nodes.forEach(detach);
			t7 = claim_space(div3_nodes);
			div1 = claim_element(div3_nodes, "DIV", { id: true, class: true });
			var div1_nodes = children(div1);

			lottie_player0 = claim_element(div1_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player0).forEach(detach);
			t8 = claim_space(div1_nodes);

			img0 = claim_element(div1_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			div1_nodes.forEach(detach);
			t9 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			a0 = claim_element(div2_nodes, "A", { class: true, href: true });
			var a0_nodes = children(a0);
			t10 = claim_text(a0_nodes, t10_value);
			a0_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t11 = claim_space(div5_nodes);
			div4 = claim_element(div5_nodes, "DIV", { id: true, class: true });
			var div4_nodes = children(div4);

			lottie_player1 = claim_element(div4_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player1).forEach(detach);
			t12 = claim_space(div4_nodes);

			img1 = claim_element(div4_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			t13 = claim_space(div14_nodes);
			div13 = claim_element(div14_nodes, "DIV", { class: true });
			var div13_nodes = children(div13);
			div6 = claim_element(div13_nodes, "DIV", { id: true, class: true });
			var div6_nodes = children(div6);

			lottie_player2 = claim_element(div6_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player2).forEach(detach);
			t14 = claim_space(div6_nodes);

			img2 = claim_element(div6_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			div6_nodes.forEach(detach);
			t15 = claim_space(div13_nodes);
			div12 = claim_element(div13_nodes, "DIV", {});
			var div12_nodes = children(div12);
			div7 = claim_element(div12_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			h61 = claim_element(div7_nodes, "H6", {});
			var h61_nodes = children(h61);
			t16 = claim_text(h61_nodes, /*content_tag_2*/ ctx[6]);
			h61_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			t17 = claim_space(div12_nodes);
			h41 = claim_element(div12_nodes, "H4", {});
			var h41_nodes = children(h41);
			t18 = claim_text(h41_nodes, /*content_title_2*/ ctx[7]);
			h41_nodes.forEach(detach);
			t19 = claim_space(div12_nodes);
			p2 = claim_element(div12_nodes, "P", { class: true });
			var p2_nodes = children(p2);
			t20 = claim_text(p2_nodes, /*content_description_2a*/ ctx[8]);
			p2_nodes.forEach(detach);
			t21 = claim_space(div12_nodes);
			div8 = claim_element(div12_nodes, "DIV", { class: true });
			var div8_nodes = children(div8);
			img3 = claim_element(div8_nodes, "IMG", { src: true, alt: true });
			t22 = claim_space(div8_nodes);
			p3 = claim_element(div8_nodes, "P", { class: true });
			var p3_nodes = children(p3);
			t23 = claim_text(p3_nodes, /*content_description_2b*/ ctx[9]);
			p3_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			t24 = claim_space(div12_nodes);
			div9 = claim_element(div12_nodes, "DIV", { class: true });
			var div9_nodes = children(div9);
			img4 = claim_element(div9_nodes, "IMG", { src: true, alt: true });
			t25 = claim_space(div9_nodes);
			p4 = claim_element(div9_nodes, "P", { class: true });
			var p4_nodes = children(p4);
			t26 = claim_text(p4_nodes, /*content_description_2c*/ ctx[10]);
			p4_nodes.forEach(detach);
			div9_nodes.forEach(detach);
			t27 = claim_space(div12_nodes);
			p5 = claim_element(div12_nodes, "P", { class: true });
			var p5_nodes = children(p5);
			t28 = claim_text(p5_nodes, /*content_description_2d*/ ctx[11]);
			p5_nodes.forEach(detach);
			t29 = claim_space(div12_nodes);
			div10 = claim_element(div12_nodes, "DIV", { id: true, class: true });
			var div10_nodes = children(div10);

			lottie_player3 = claim_element(div10_nodes, "LOTTIE-PLAYER", {
				autoplay: true,
				loop: true,
				mode: true,
				class: true,
				src: true
			});

			children(lottie_player3).forEach(detach);
			t30 = claim_space(div10_nodes);

			img5 = claim_element(div10_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			div10_nodes.forEach(detach);
			t31 = claim_space(div12_nodes);
			div11 = claim_element(div12_nodes, "DIV", { class: true });
			var div11_nodes = children(div11);
			a1 = claim_element(div11_nodes, "A", { class: true, href: true });
			var a1_nodes = children(a1);
			t32 = claim_text(a1_nodes, t32_value);
			a1_nodes.forEach(detach);
			div11_nodes.forEach(detach);
			div12_nodes.forEach(detach);
			div13_nodes.forEach(detach);
			div14_nodes.forEach(detach);
			div15_nodes.forEach(detach);
			div16_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "tag-pink-large svelte-1esknib");
			attr(p0, "class", "p-medium");
			attr(p1, "class", "p-medium");
			set_custom_element_data(lottie_player0, "autoplay", "");
			set_custom_element_data(lottie_player0, "loop", "");
			set_custom_element_data(lottie_player0, "mode", "normal");
			set_custom_element_data(lottie_player0, "class", "lottie-1 svelte-1esknib");
			if (!src_url_equal(lottie_player0.src, lottie_player0_src_value = eyeLottie)) set_custom_element_data(lottie_player0, "src", lottie_player0_src_value);
			attr(img0, "id", "content-image-1");
			if (!src_url_equal(img0.src, img0_src_value = /*content_image_1*/ ctx[4].url)) attr(img0, "src", img0_src_value);
			attr(img0, "alt", img0_alt_value = /*content_image_1*/ ctx[4].alt);
			attr(img0, "class", "svelte-1esknib");
			attr(div1, "id", "content-image-mobile-1");
			attr(div1, "class", "svelte-1esknib");
			attr(a0, "class", "primary-large-button svelte-1esknib");
			attr(a0, "href", a0_href_value = /*content_action_1*/ ctx[5].url);
			attr(div2, "class", "button-wrapper svelte-1esknib");
			set_custom_element_data(lottie_player1, "autoplay", "");
			set_custom_element_data(lottie_player1, "loop", "");
			set_custom_element_data(lottie_player1, "mode", "normal");
			set_custom_element_data(lottie_player1, "class", "lottie-1 svelte-1esknib");
			if (!src_url_equal(lottie_player1.src, lottie_player1_src_value = eyeLottie)) set_custom_element_data(lottie_player1, "src", lottie_player1_src_value);
			attr(img1, "id", "content-image-1");
			if (!src_url_equal(img1.src, img1_src_value = /*content_image_1*/ ctx[4].url)) attr(img1, "src", img1_src_value);
			attr(img1, "alt", img1_alt_value = /*content_image_1*/ ctx[4].alt);
			attr(img1, "class", "svelte-1esknib");
			attr(div4, "id", "content-image-desktop-1");
			attr(div4, "class", "svelte-1esknib");
			attr(div5, "class", "section-container content svelte-1esknib");
			set_custom_element_data(lottie_player2, "autoplay", "");
			set_custom_element_data(lottie_player2, "loop", "");
			set_custom_element_data(lottie_player2, "mode", "normal");
			set_custom_element_data(lottie_player2, "class", "lottie-2 svelte-1esknib");
			if (!src_url_equal(lottie_player2.src, lottie_player2_src_value = piebarchartLottie)) set_custom_element_data(lottie_player2, "src", lottie_player2_src_value);
			attr(img2, "id", "content-image-2");
			if (!src_url_equal(img2.src, img2_src_value = /*content_image_2*/ ctx[12].url)) attr(img2, "src", img2_src_value);
			attr(img2, "alt", img2_alt_value = /*content_image_2*/ ctx[12].alt);
			attr(img2, "class", "svelte-1esknib");
			attr(div6, "id", "content-image-desktop-2");
			attr(div6, "class", "svelte-1esknib");
			attr(div7, "class", "tag-yellow-large svelte-1esknib");
			attr(p2, "class", "p-medium");
			if (!src_url_equal(img3.src, img3_src_value = /*checkmark*/ ctx[14].url)) attr(img3, "src", img3_src_value);
			attr(img3, "alt", img3_alt_value = /*checkmark*/ ctx[14].alt);
			attr(p3, "class", "p-medium");
			attr(div8, "class", "content-wrapper svelte-1esknib");
			if (!src_url_equal(img4.src, img4_src_value = /*checkmark*/ ctx[14].url)) attr(img4, "src", img4_src_value);
			attr(img4, "alt", img4_alt_value = /*checkmark*/ ctx[14].alt);
			attr(p4, "class", "p-medium");
			attr(div9, "class", "content-wrapper svelte-1esknib");
			attr(p5, "class", "p-medium");
			set_custom_element_data(lottie_player3, "autoplay", "");
			set_custom_element_data(lottie_player3, "loop", "");
			set_custom_element_data(lottie_player3, "mode", "normal");
			set_custom_element_data(lottie_player3, "class", "lottie-2 svelte-1esknib");
			if (!src_url_equal(lottie_player3.src, lottie_player3_src_value = piebarchartLottie)) set_custom_element_data(lottie_player3, "src", lottie_player3_src_value);
			attr(img5, "id", "content-image-2");
			if (!src_url_equal(img5.src, img5_src_value = /*content_image_2*/ ctx[12].url)) attr(img5, "src", img5_src_value);
			attr(img5, "alt", img5_alt_value = /*content_image_2*/ ctx[12].alt);
			attr(img5, "class", "svelte-1esknib");
			attr(div10, "id", "content-image-mobile-2");
			attr(div10, "class", "svelte-1esknib");
			attr(a1, "class", "primary-large-button svelte-1esknib");
			attr(a1, "href", a1_href_value = /*content_action_2*/ ctx[13].url);
			attr(div11, "class", "button-wrapper svelte-1esknib");
			attr(div13, "class", "section-container content svelte-1esknib");
			attr(div14, "class", "wrapper svelte-1esknib");
			attr(div15, "class", "container svelte-1esknib");
			attr(div16, "class", "section");
			attr(div16, "id", "section-c289173c");
		},
		m(target, anchor) {
			insert_hydration(target, div16, anchor);
			append_hydration(div16, div15);
			append_hydration(div15, div14);
			append_hydration(div14, div5);
			append_hydration(div5, div3);
			append_hydration(div3, div0);
			append_hydration(div0, h60);
			append_hydration(h60, t0);
			append_hydration(div3, t1);
			append_hydration(div3, h40);
			append_hydration(h40, t2);
			append_hydration(div3, t3);
			append_hydration(div3, p0);
			append_hydration(p0, t4);
			append_hydration(div3, t5);
			append_hydration(div3, p1);
			append_hydration(p1, t6);
			append_hydration(div3, t7);
			append_hydration(div3, div1);
			append_hydration(div1, lottie_player0);
			append_hydration(div1, t8);
			append_hydration(div1, img0);
			append_hydration(div3, t9);
			append_hydration(div3, div2);
			append_hydration(div2, a0);
			append_hydration(a0, t10);
			append_hydration(div5, t11);
			append_hydration(div5, div4);
			append_hydration(div4, lottie_player1);
			append_hydration(div4, t12);
			append_hydration(div4, img1);
			append_hydration(div14, t13);
			append_hydration(div14, div13);
			append_hydration(div13, div6);
			append_hydration(div6, lottie_player2);
			append_hydration(div6, t14);
			append_hydration(div6, img2);
			append_hydration(div13, t15);
			append_hydration(div13, div12);
			append_hydration(div12, div7);
			append_hydration(div7, h61);
			append_hydration(h61, t16);
			append_hydration(div12, t17);
			append_hydration(div12, h41);
			append_hydration(h41, t18);
			append_hydration(div12, t19);
			append_hydration(div12, p2);
			append_hydration(p2, t20);
			append_hydration(div12, t21);
			append_hydration(div12, div8);
			append_hydration(div8, img3);
			append_hydration(div8, t22);
			append_hydration(div8, p3);
			append_hydration(p3, t23);
			append_hydration(div12, t24);
			append_hydration(div12, div9);
			append_hydration(div9, img4);
			append_hydration(div9, t25);
			append_hydration(div9, p4);
			append_hydration(p4, t26);
			append_hydration(div12, t27);
			append_hydration(div12, p5);
			append_hydration(p5, t28);
			append_hydration(div12, t29);
			append_hydration(div12, div10);
			append_hydration(div10, lottie_player3);
			append_hydration(div10, t30);
			append_hydration(div10, img5);
			append_hydration(div12, t31);
			append_hydration(div12, div11);
			append_hydration(div11, a1);
			append_hydration(a1, t32);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_tag_1*/ 1) set_data(t0, /*content_tag_1*/ ctx[0]);
			if (dirty & /*content_title_1*/ 2) set_data(t2, /*content_title_1*/ ctx[1]);
			if (dirty & /*content_description_1a*/ 4) set_data(t4, /*content_description_1a*/ ctx[2]);
			if (dirty & /*content_description_1b*/ 8) set_data(t6, /*content_description_1b*/ ctx[3]);

			if (dirty & /*content_image_1*/ 16 && !src_url_equal(img0.src, img0_src_value = /*content_image_1*/ ctx[4].url)) {
				attr(img0, "src", img0_src_value);
			}

			if (dirty & /*content_image_1*/ 16 && img0_alt_value !== (img0_alt_value = /*content_image_1*/ ctx[4].alt)) {
				attr(img0, "alt", img0_alt_value);
			}

			if (dirty & /*content_action_1*/ 32 && t10_value !== (t10_value = /*content_action_1*/ ctx[5].label + "")) set_data(t10, t10_value);

			if (dirty & /*content_action_1*/ 32 && a0_href_value !== (a0_href_value = /*content_action_1*/ ctx[5].url)) {
				attr(a0, "href", a0_href_value);
			}

			if (dirty & /*content_image_1*/ 16 && !src_url_equal(img1.src, img1_src_value = /*content_image_1*/ ctx[4].url)) {
				attr(img1, "src", img1_src_value);
			}

			if (dirty & /*content_image_1*/ 16 && img1_alt_value !== (img1_alt_value = /*content_image_1*/ ctx[4].alt)) {
				attr(img1, "alt", img1_alt_value);
			}

			if (dirty & /*content_image_2*/ 4096 && !src_url_equal(img2.src, img2_src_value = /*content_image_2*/ ctx[12].url)) {
				attr(img2, "src", img2_src_value);
			}

			if (dirty & /*content_image_2*/ 4096 && img2_alt_value !== (img2_alt_value = /*content_image_2*/ ctx[12].alt)) {
				attr(img2, "alt", img2_alt_value);
			}

			if (dirty & /*content_tag_2*/ 64) set_data(t16, /*content_tag_2*/ ctx[6]);
			if (dirty & /*content_title_2*/ 128) set_data(t18, /*content_title_2*/ ctx[7]);
			if (dirty & /*content_description_2a*/ 256) set_data(t20, /*content_description_2a*/ ctx[8]);

			if (dirty & /*checkmark*/ 16384 && !src_url_equal(img3.src, img3_src_value = /*checkmark*/ ctx[14].url)) {
				attr(img3, "src", img3_src_value);
			}

			if (dirty & /*checkmark*/ 16384 && img3_alt_value !== (img3_alt_value = /*checkmark*/ ctx[14].alt)) {
				attr(img3, "alt", img3_alt_value);
			}

			if (dirty & /*content_description_2b*/ 512) set_data(t23, /*content_description_2b*/ ctx[9]);

			if (dirty & /*checkmark*/ 16384 && !src_url_equal(img4.src, img4_src_value = /*checkmark*/ ctx[14].url)) {
				attr(img4, "src", img4_src_value);
			}

			if (dirty & /*checkmark*/ 16384 && img4_alt_value !== (img4_alt_value = /*checkmark*/ ctx[14].alt)) {
				attr(img4, "alt", img4_alt_value);
			}

			if (dirty & /*content_description_2c*/ 1024) set_data(t26, /*content_description_2c*/ ctx[10]);
			if (dirty & /*content_description_2d*/ 2048) set_data(t28, /*content_description_2d*/ ctx[11]);

			if (dirty & /*content_image_2*/ 4096 && !src_url_equal(img5.src, img5_src_value = /*content_image_2*/ ctx[12].url)) {
				attr(img5, "src", img5_src_value);
			}

			if (dirty & /*content_image_2*/ 4096 && img5_alt_value !== (img5_alt_value = /*content_image_2*/ ctx[12].alt)) {
				attr(img5, "alt", img5_alt_value);
			}

			if (dirty & /*content_action_2*/ 8192 && t32_value !== (t32_value = /*content_action_2*/ ctx[13].label + "")) set_data(t32, t32_value);

			if (dirty & /*content_action_2*/ 8192 && a1_href_value !== (a1_href_value = /*content_action_2*/ ctx[13].url)) {
				attr(a1, "href", a1_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div16);
		}
	};
}

const eyeLottie = '{"nm":"Comp 10","ddd":0,"h":500,"w":500,"meta":{"g":"@lottiefiles/toolkit-js 0.26.1"},"layers":[{"ty":4,"nm":"Layer 3","sr":1,"st":0,"op":100,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,31.128,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,0,100],"t":5},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,100,100],"t":10},{"o":{"x":0.167,"y":0},"i":{"x":0.085,"y":1},"s":[100,100,100],"t":65},{"s":[100,0,100],"t":70}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[250,281.128,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2","nm":"Kleaner","ix":1,"en":1,"ef":[{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0001","nm":"Anticipation","ix":1,"v":{"a":0,"k":0,"ix":1}},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0002","nm":"Smart Interpolation","ix":2,"v":{"a":0,"k":0,"ix":2}},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0003","nm":"Follow Through","ix":3,"v":{"a":0,"k":1,"ix":3}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0004","nm":"Anticipation","ix":4,"v":0},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0005","nm":"Duration (s)","ix":5,"v":{"a":0,"k":0.3,"ix":5}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0006","nm":"Amplitude","ix":6,"v":{"a":0,"k":50,"ix":6}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0007","nm":"","ix":7,"v":0},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0008","nm":"Interpolation","ix":8,"v":0},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0009","nm":"Slow In","ix":9,"v":{"a":0,"k":60,"ix":9}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0010","nm":"Slow Out","ix":10,"v":{"a":0,"k":25,"ix":10}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0011","nm":"","ix":11,"v":0},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0012","nm":"Follow Through","ix":12,"v":0},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0013","nm":"Elasticity","ix":13,"v":{"a":0,"k":10,"ix":13}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0014","nm":"Elasticity random","ix":14,"v":{"a":0,"k":0,"ix":14}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0015","nm":"Damping","ix":15,"v":{"a":0,"k":50,"ix":15}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0016","nm":"Damping random","ix":16,"v":{"a":0,"k":0,"ix":16}},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0017","nm":"Bounce","ix":17,"v":{"a":0,"k":0,"ix":17}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0018","nm":"","ix":18,"v":0},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0019","nm":"Spatial Options","ix":19,"v":0},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0020","nm":"Smart Interpolation","ix":20,"v":{"a":0,"k":0,"ix":20}},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0021","nm":"Mode","ix":21,"v":{"a":0,"k":1,"ix":21}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0022","nm":"Overlap (simulation)","ix":22,"v":0},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0023","nm":"Overlap","ix":23,"v":{"a":0,"k":1,"ix":23}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0024","nm":"Delay (s)","ix":24,"v":{"a":0,"k":0.05,"ix":24}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0025","nm":"Overlap random","ix":25,"v":{"a":0,"k":0,"ix":25}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0026","nm":"","ix":26,"v":0},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0027","nm":"Soft Body (simulation)","ix":27,"v":0},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0028","nm":"Soft Body","ix":28,"v":{"a":0,"k":1,"ix":28}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0029","nm":"Soft-Body Flexibility","ix":29,"v":{"a":0,"k":100,"ix":29}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0030","nm":"","ix":30,"v":0},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0031","nm":"","ix":31,"v":0},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0032","nm":"Precision","ix":32,"v":{"a":0,"k":1,"ix":32}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[7.276,5.296],[0,-5.879],[16.087,0],[4.807,3.499],[-10.208,0],[0,16.088]],"o":[[2.996,4.578],[0,16.088],[-6.4,0],[5.202,7.948],[16.088,0],[0,-9.687]],"v":[[17.105,7.586],[21.857,23.506],[-7.271,52.635],[-24.377,47.047],[0,60.257],[29.129,31.128]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.8706,0.8745,0.9843],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":2,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,-16.087],[16.087,0],[0,16.087],[-16.087,0]],"o":[[0,16.087],[-16.087,0],[0,-16.087],[16.087,0]],"v":[[29.129,31.128],[0,60.257],[-29.129,31.128],[0,1.999]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9529,0.9451,0.9882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 6","ix":2,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":1,"cix":2,"np":6,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[1.539,9.116],[0,0],[-9.441,-7.589],[0,0]],"o":[[0,0],[1.7,12.569],[0,0],[-6.706,-5.808]],"v":[[-38.429,37.63],[-47.902,37.63],[-30.251,68.836],[-25.492,60.595]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.3137,0.6784,0.7451],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":2,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-1.7,12.57],[0,0],[6.707,-5.809],[0,0]],"o":[[0,0],[-1.539,9.116],[0,0],[9.443,-7.589]],"v":[[47.902,37.63],[38.428,37.63],[25.49,60.597],[30.248,68.838]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.3137,0.6784,0.7451],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":3,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-6.66,5.602],[0,0],[1.959,-12.297],[0,0]],"o":[[0,0],[-9.394,7.374],[0,0],[1.761,-8.853]],"v":[[-25.069,1.275],[-29.799,-6.919],[-47.731,23.506],[-38.257,23.506]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.3137,0.6784,0.7451],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 4","ix":4,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[4.681,0],[4.162,1.518],[0,0],[-6.389,0],[-5.589,2.259],[0,0]],"o":[[-4.681,0],[0,0],[5.588,2.259],[6.389,0],[0,0],[-4.162,1.518]],"v":[[-0.002,70.141],[-13.315,67.752],[-18.068,75.984],[-0.002,79.517],[18.065,75.984],[13.312,67.753]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.3137,0.6784,0.7451],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 5","ix":5,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-4.481,0],[-4.01,-1.396],[0,0],[6.189,0],[5.444,-2.127],[0,0]],"o":[[4.481,0],[0,0],[-5.445,-2.126],[-6.188,0],[0,0],[4.01,-1.397]],"v":[[-0.002,-7.885],[12.778,-5.692],[17.531,-13.924],[-0.002,-17.261],[-17.534,-13.924],[-12.782,-5.692]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.3137,0.6784,0.7451],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 6","ix":6,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-1.761,-8.854],[0,0],[9.396,7.374],[0,0]],"o":[[0,0],[-1.959,-12.298],[0,0],[6.661,5.602]],"v":[[38.257,23.506],[47.731,23.506],[29.797,-6.92],[25.066,1.274]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.3137,0.6784,0.7451],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,31.128],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,31.128],"ix":2},"r":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[0],"t":10},{"s":[300],"t":75}],"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":3,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,20.391],[14.952,11.601],[12.999,0],[12.807,-2.208],[0,-20.393],[-14.958,-11.601],[-25.616,4.418]],"o":[[0,-20.39],[-12.808,-2.211],[-13.003,0],[-14.954,11.601],[0,20.395],[25.614,4.414],[14.953,-11.601]],"v":[[63.417,31.146],[38.804,-18.938],[0.003,-22.291],[-38.798,-18.942],[-63.417,31.146],[-38.793,81.238],[38.802,81.232]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.4118,0.7882,0.8588],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 4","ix":4,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,16.088],[2.996,4.578],[6.401,0],[0,-16.087],[-2.996,-4.578],[-6.4,0]],"o":[[0,-5.879],[-4.806,-3.499],[-16.087,0],[0,5.879],[4.807,3.499],[16.087,0]],"v":[[21.857,23.506],[17.105,7.586],[0,1.999],[-29.128,31.128],[-24.377,47.047],[-7.271,52.635]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9529,0.9451,0.9882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 5","ix":5,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-16.087,0],[-4.806,-3.499],[10.208,0],[0,-16.087],[-7.276,-5.296],[0,5.879]],"o":[[6.401,0],[-5.201,-7.948],[-16.088,0],[0,9.687],[-2.996,-4.578],[0,-16.087]],"v":[[0,1.999],[17.105,7.586],[-7.271,-5.623],[-36.4,23.506],[-24.377,47.047],[-29.128,31.128]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9529,0.9451,0.9882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":1},{"ty":4,"nm":"Layer 2","sr":1,"st":0,"op":100,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,31.146,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,3,100],"t":5},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,100,100],"t":10},{"o":{"x":0.167,"y":0},"i":{"x":0.085,"y":1},"s":[100,100,100],"t":65},{"s":[100,3,100],"t":70}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[250,281.146,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2","nm":"Kleaner","ix":1,"en":1,"ef":[{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0001","nm":"Anticipation","ix":1,"v":{"a":0,"k":0,"ix":1}},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0002","nm":"Smart Interpolation","ix":2,"v":{"a":0,"k":0,"ix":2}},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0003","nm":"Follow Through","ix":3,"v":{"a":0,"k":1,"ix":3}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0004","nm":"Anticipation","ix":4,"v":0},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0005","nm":"Duration (s)","ix":5,"v":{"a":0,"k":0.3,"ix":5}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0006","nm":"Amplitude","ix":6,"v":{"a":0,"k":50,"ix":6}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0007","nm":"","ix":7,"v":0},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0008","nm":"Interpolation","ix":8,"v":0},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0009","nm":"Slow In","ix":9,"v":{"a":0,"k":60,"ix":9}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0010","nm":"Slow Out","ix":10,"v":{"a":0,"k":25,"ix":10}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0011","nm":"","ix":11,"v":0},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0012","nm":"Follow Through","ix":12,"v":0},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0013","nm":"Elasticity","ix":13,"v":{"a":0,"k":10,"ix":13}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0014","nm":"Elasticity random","ix":14,"v":{"a":0,"k":0,"ix":14}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0015","nm":"Damping","ix":15,"v":{"a":0,"k":50,"ix":15}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0016","nm":"Damping random","ix":16,"v":{"a":0,"k":0,"ix":16}},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0017","nm":"Bounce","ix":17,"v":{"a":0,"k":0,"ix":17}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0018","nm":"","ix":18,"v":0},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0019","nm":"Spatial Options","ix":19,"v":0},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0020","nm":"Smart Interpolation","ix":20,"v":{"a":0,"k":0,"ix":20}},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0021","nm":"Mode","ix":21,"v":{"a":0,"k":1,"ix":21}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0022","nm":"Overlap (simulation)","ix":22,"v":0},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0023","nm":"Overlap","ix":23,"v":{"a":0,"k":1,"ix":23}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0024","nm":"Delay (s)","ix":24,"v":{"a":0,"k":0.05,"ix":24}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0025","nm":"Overlap random","ix":25,"v":{"a":0,"k":0,"ix":25}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0026","nm":"","ix":26,"v":0},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0027","nm":"Soft Body (simulation)","ix":27,"v":0},{"ty":7,"mn":"Pseudo/Duik Kleaner v3.2-0028","nm":"Soft Body","ix":28,"v":{"a":0,"k":1,"ix":28}},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0029","nm":"Soft-Body Flexibility","ix":29,"v":{"a":0,"k":100,"ix":29}},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0030","nm":"","ix":30,"v":0},{"ty":6,"mn":"Pseudo/Duik Kleaner v3.2-0031","nm":"","ix":31,"v":0},{"ty":0,"mn":"Pseudo/Duik Kleaner v3.2-0032","nm":"Precision","ix":32,"v":{"a":0,"k":1,"ix":32}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[15.846,-4.881],[-16.389,-2.696]],"o":[[17.258,-0.775],[-13.368,-6.706]],"v":[[-28.621,-28.072],[21.349,-26.915]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,1,1],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":2,"cix":2,"np":1,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-1.132,-0.906],[-77.286,61.807],[4.934,3.945],[6.46,4.061],[108.324,50.329]],"o":[[77.246,61.809],[4.934,-3.945],[-6.014,-4.808],[-35.472,20.354],[0.612,1.094]],"v":[[-135.89,38.226],[135.887,38.229],[135.886,24.073],[117.133,10.816],[-138.475,35.187]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9529,0.9451,0.9882],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":3,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[4.934,3.945],[48.621,0],[38.606,-30.892],[-4.929,-3.944],[-77.286,61.807]],"o":[[-38.64,-30.891],[-48.663,0],[-4.928,3.944],[77.246,61.809],[4.934,-3.945]],"v":[[135.886,24.073],[0.003,-22.291],[-135.891,24.075],[-135.89,38.225],[135.887,38.229]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9725,0.9765,0.9961],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 4","ix":4,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[5.131,4.961],[50.561,0],[40.146,-38.851],[-5.126,-4.96],[-80.369,77.731]],"o":[[-40.182,-38.85],[-50.605,0],[-5.125,4.96],[80.328,77.734],[5.131,-4.962]],"v":[[141.308,22.251],[0.003,-36.059],[-141.312,22.253],[-141.311,40.049],[141.309,40.054]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9216,0.7137,0.0235],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":2},{"ty":4,"nm":"Layer 1","sr":1,"st":0,"op":100,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[250,250,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[5.131,5.981],[50.561,0],[40.146,-46.843],[-5.126,-5.981],[-80.369,93.72]],"o":[[-40.182,-46.841],[-50.605,0],[-5.125,5.981],[80.328,93.724],[5.131,-5.982]],"v":[[141.308,20.421],[0.003,-49.883],[-141.312,20.424],[-141.311,41.881],[141.309,41.886]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9686,0.8235,0.3294],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":2,"cix":2,"np":8,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[1.336,-1.064],[0,0],[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0],[0,0],[-1.936,-1.05]],"v":[[-148.076,-31.364],[-77.301,7.018],[-90.013,25.626],[-86.296,28.79],[-71.421,7.018],[-142.934,-31.764]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9216,0.7137,0.0235],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":2,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[1.592,-1.274],[-0.015,-0.013],[0,0],[0,0],[0,0],[0,0],[0,0]],"o":[[-2.026,-1.673],[0.016,0.013],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]],"v":[[-116.241,-68.646],[-122.169,-68.673],[-122.12,-68.646],[-59.384,-16.861],[-74.864,-1.597],[-72.278,1.651],[-55.017,-15.37],[-56.23,-19.111]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9216,0.7137,0.0235],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":3,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[2.078,-1.565],[-0.322,-0.56],[0,0],[0,0],[0,0],[0,0],[0,0]],"o":[[0.422,0.356],[0,0],[0,0],[0,0],[0,0],[0,0],[-1.673,-2.909]],"v":[[-72.626,-97.925],[-71.486,-96.587],[-30.876,-25.99],[-49.849,-17.565],[-49.109,-15.283],[-24.997,-25.99],[-65.607,-96.587]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9216,0.7137,0.0235],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 4","ix":4,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[5.019,-2.721],[0,0],[2.669,-2.272],[0,0],[0,0],[0,0]],"o":[[0,0],[2.125,1.692],[0,0],[0,0],[0,0],[4.347,-3.7]],"v":[[142.934,-31.764],[142.197,-31.365],[142.401,-23.968],[84.135,25.626],[86.296,28.79],[148.28,-23.968]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9216,0.7137,0.0235],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 5","ix":5,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[1.919,-2.41],[0,0],[0,0],[0,0],[4.397,-3.554]],"o":[[0,0],[0,0],[0,0],[3.543,-4.449],[1.866,1.493]],"v":[[117.104,-62.021],[68.985,-1.597],[72.278,1.651],[122.983,-62.021],[116.289,-68.673]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9216,0.7137,0.0235],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 6","ix":6,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0],[3.309,-2.794],[0.726,-2.238],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[1.562,-4.816],[1.457,1.097],[0,0],[0,0],[0,0]],"v":[[49.137,-15.37],[47.626,-16.861],[50.351,-19.111],[74.246,-92.751],[66.748,-97.925],[68.367,-92.751],[43.97,-17.565],[49.109,-15.283]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9216,0.7137,0.0235],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 7","ix":7,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[2.628,-1.991],[-0.156,-1.489],[0,0],[0,0],[0,0]],"o":[[0.934,0.708],[0,0],[0,0],[0,0],[-0.438,-4.188]],"v":[[-2.939,-111.189],[-1.153,-107.917],[7.311,-26.915],[13.191,-26.915],[4.727,-107.917]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9216,0.7137,0.0235],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 8","ix":8,"cix":2,"np":7,"it":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-4.347,-3.7],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[-5.017,-2.721]],"v":[[-148.28,-23.968],[-86.296,28.79],[-71.421,7.018],[-142.934,-31.764]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9686,0.8235,0.3294],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 2","ix":2,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-3.557,-4.466],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[-4.402,-3.634]],"v":[[-122.983,-62.021],[-72.278,1.651],[-53.505,-16.861],[-116.241,-68.646]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9686,0.8235,0.3294],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 3","ix":3,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[-1.762,-5.43],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[-2.846,-4.948]],"v":[[-74.246,-92.751],[-49.109,-15.283],[-24.997,-25.99],[-65.607,-96.587]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9686,0.8235,0.3294],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 4","ix":4,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[5.019,-2.721],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[4.347,-3.7]],"v":[[142.934,-31.764],[71.422,7.018],[86.296,28.79],[148.28,-23.968]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9686,0.8235,0.3294],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 5","ix":5,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[4.402,-3.634],[0,0],[0,0]],"o":[[3.556,-4.466],[0,0],[0,0],[0,0]],"v":[[122.983,-62.021],[116.241,-68.646],[53.505,-16.861],[72.278,1.651]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9686,0.8235,0.3294],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 6","ix":6,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[2.846,-4.948],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[1.761,-5.43]],"v":[[65.607,-96.587],[24.997,-25.99],[49.109,-15.283],[74.246,-92.751]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9686,0.8235,0.3294],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Group 7","ix":7,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0.593,-5.678],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[-0.593,-5.678]],"v":[[-4.726,-107.917],[-13.19,-26.915],[13.191,-26.915],[4.727,-107.917]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9686,0.8235,0.3294],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":3}],"v":"5.7.11","fr":25,"op":79,"ip":0,"assets":[]}';
const piebarchartLottie = '{"nm":"___c","ddd":0,"h":1080,"w":1200,"meta":{"g":"@lottiefiles/toolkit-js 0.26.1"},"layers":[{"ty":0,"nm":"Comp 4","sr":1,"st":0,"op":253,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[960,540,0],"ix":1},"s":{"a":0,"k":[125,125,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[600,540,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"w":1920,"h":1080,"refId":"comp_24","ind":1}],"v":"5.1.3","fr":30,"op":253,"ip":0,"assets":[{"nm":"","id":"comp_24","layers":[{"ty":0,"nm":"infogr seamless 2","sr":1,"st":0,"op":253,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[960,540,0],"ix":1},"s":{"a":0,"k":[199.259,199.259,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[748,688,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"w":1920,"h":1080,"refId":"comp_25","ind":1}]},{"nm":"","id":"comp_25","layers":[{"ty":4,"nm":"vert line","sr":1,"st":-11,"op":253,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[101,-46.5,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[0,0,100],"t":179},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,100,100],"t":190},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,100,100],"t":246},{"s":[0,100,100],"t":252}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1061,493.5,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[0,-8],[0,0]],"o":[[0,37],[0,0]],"v":[[101,-183],[101,90]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":1},{"ty":4,"nm":"line 5","sr":1,"st":175,"op":253,"ip":175,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-40,71,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[920,611,0],"t":185,"ti":[0,0,0],"to":[0,0,0]},{"s":[920,587,0],"t":199}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.24,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-40,71],[258.5,71]]}],"t":185},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-18,70.509],[216.5,70.509]]}],"t":202},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[33,70.21],[245.5,70.21]]}],"t":218},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[33,70.21],[245.5,70.21]]}],"t":230},{"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-29,70.47],[29.5,70.47]]}],"t":247}],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[5],"t":185},{"s":[44],"t":199}],"ix":5},"c":{"a":0,"k":[1,0.3098,0.6392],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":2},{"ty":4,"nm":"line 4","sr":1,"st":175,"op":248,"ip":175,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-40,71,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[920,611,0],"t":182,"ti":[0,0,0],"to":[0,0,0]},{"s":[920,526,0],"t":196}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.24,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-40,71],[258.5,71]]}],"t":183},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[27,70.743],[176.5,70.743]]}],"t":201},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-32,71.046],[188.5,71.046]]}],"t":214},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[99,71.163],[188.5,71.046]]}],"t":229},{"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[99,71.163],[101.5,71.282]]}],"t":250}],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[5],"t":182},{"s":[44],"t":196}],"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":3},{"ty":4,"nm":"line 3","sr":1,"st":175,"op":248,"ip":175,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-40,71,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[920,611,0],"t":179,"ti":[0,0,0],"to":[0,0,0]},{"s":[920,466,0],"t":193}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.15,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-40,71],[258.5,71]]}],"t":179},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[51,70.591],[241.5,70.773]]}],"t":196},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[16,70.645],[218.5,71.009]]}],"t":214},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[100,70.641],[218.5,71.009]]}],"t":229},{"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[100,70.641],[101.938,70.705]]}],"t":250}],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[5],"t":179},{"s":[44],"t":193}],"ix":5},"c":{"a":0,"k":[0.9647,0.898,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":4},{"ty":4,"nm":"line 2","sr":1,"st":175,"op":248,"ip":175,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-40,71,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[920,611,0],"t":175,"ti":[0,0,0],"to":[0,0,0]},{"s":[920,406,0],"t":189}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.15,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-40,71],[258.5,71]]}],"t":176},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-14,70.914],[201.5,70.914]]}],"t":194},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-14,70.914],[257.5,70.91]]}],"t":214},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[99,71.339],[257.5,70.91]]}],"t":229},{"s":[{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[99,71.339],[102.625,71.32]]}],"t":250}],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[5],"t":175},{"s":[44],"t":189}],"ix":5},"c":{"a":0,"k":[0.4118,0.7882,0.8588],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":5},{"ty":4,"nm":"mask2","sr":1,"st":-11,"op":243,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"td":1,"ao":0,"ks":{"a":{"a":0,"k":[88.5,103.5,0],"ix":1},"s":{"a":0,"k":[100,387.324,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[88.5,207.5,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[184.5,-35.5],[185,84.038],[-184,84.038],[-184.5,-35.5]]},"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.1882,0.3725,0.5765],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[88.5,103.5],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":6,"parent":5},{"ty":0,"nm":"Pre-comp 3","sr":1,"st":-11,"op":243,"ip":0,"hd":false,"ddd":0,"bm":0,"tt":2,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[960,540,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[960,540,0],"t":174,"ti":[0,0,0],"to":[0,0,0]},{"s":[960,674,0],"t":189}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"w":1920,"h":1080,"refId":"comp_26","ind":7},{"ty":4,"nm":"graph1","sr":1,"st":-11,"op":243,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[108.5,-95.5,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1068.5,434.5,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]],"v":[[-29,-35.25],[2.5,-35.5],[33.5,-69],[70.5,-69],[110.5,-115.5],[143.5,-115.5],[182,-155.5],[246,-155.5]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":9,"ix":5},"c":{"a":0,"k":[1,0.3098,0.6392],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":1,"k":[{"o":{"x":0.69,"y":0},"i":{"x":0.31,"y":1},"s":[0],"t":16},{"s":[100],"t":43}],"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":1,"k":[{"o":{"x":0.69,"y":0},"i":{"x":0.31,"y":1},"s":[0],"t":50},{"s":[100],"t":70}],"ix":1},"m":1}],"ind":8},{"ty":4,"nm":"line","sr":1,"st":-11,"op":176,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-40,71,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.41,"y":1},"s":[0,100,100],"t":-11},{"o":{"x":0.59,"y":0},"i":{"x":0.833,"y":1},"s":[100,100,100],"t":24},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[100,100,100],"t":88},{"o":{"x":0.164,"y":0},"i":{"x":0.833,"y":1},"s":[100,0,100],"t":95},{"o":{"x":0.164,"y":0},"i":{"x":0.698,"y":0.994},"s":[100,0,100],"t":133},{"o":{"x":0.167,"y":0.167},"i":{"x":0.26,"y":1},"s":[0,100,100],"t":134},{"s":[100,100,100],"t":158}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[920,611,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 2","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[0,0]],"o":[[0,0]],"v":[[348.5,-9]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":2,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-40,71],[258.5,71]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":9},{"ty":4,"nm":"line 6","sr":1,"st":242,"op":253,"ip":247,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-40,71,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.41,"y":1},"s":[0,100,100],"t":242},{"o":{"x":0.59,"y":0},"i":{"x":0.833,"y":1},"s":[100,100,100],"t":277},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[100,100,100],"t":341},{"o":{"x":0.164,"y":0},"i":{"x":0.833,"y":1},"s":[100,0,100],"t":348},{"o":{"x":0.164,"y":0},"i":{"x":0.698,"y":0.994},"s":[100,0,100],"t":386},{"o":{"x":0.167,"y":0.167},"i":{"x":0.26,"y":1},"s":[0,100,100],"t":387},{"s":[100,100,100],"t":411}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[920,611,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 2","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[0,0]],"o":[[0,0]],"v":[[348.5,-9]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":2,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[-40,71],[258.5,71]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":10},{"ty":4,"nm":"bar5","sr":1,"st":242,"op":253,"ip":247,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-3.158,38.756,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,0,100],"t":242},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,64,100],"t":252},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,64,100],"t":311},{"s":[100,0,100],"t":323}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[960,611.483,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[60.287,146.411],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-3.158,-34.45],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":11},{"ty":4,"nm":"bar8","sr":1,"st":242,"op":253,"ip":247,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-3.158,38.756,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,0,100],"t":250},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,87,100],"t":260},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,87,100],"t":311},{"s":[100,0,100],"t":323}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.29,"y":1},"s":[960,611.483,0],"t":250,"ti":[-12,0,0],"to":[12,0,0]},{"s":[1032,611.483,0],"t":260}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[60.287,146.411],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-3.158,-34.45],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":12},{"ty":4,"nm":"bar7","sr":1,"st":242,"op":253,"ip":247,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-3.158,38.756,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,0,100],"t":258},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,117,100],"t":268},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,117,100],"t":311},{"s":[100,0,100],"t":323}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.29,"y":1},"s":[1032,611.483,0],"t":258,"ti":[-12,0,0],"to":[12,0,0]},{"s":[1104,611.483,0],"t":268}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[60.287,146.411],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.2314,0.4392,0.6745],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-3.158,-34.45],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":13},{"ty":4,"nm":"bar6","sr":1,"st":242,"op":253,"ip":247,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-3.158,38.756,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,0,100],"t":266},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,146,100],"t":276},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,146,100],"t":311},{"s":[100,0,100],"t":323}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.29,"y":1},"s":[1104,611.483,0],"t":266,"ti":[-12,0,0],"to":[12,0,0]},{"s":[1176,611.483,0],"t":276}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[60.287,146.411],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.1882,0.3725,0.5765],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-3.158,-34.45],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":14},{"ty":4,"nm":"bar4","sr":1,"st":-11,"op":70,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-3.158,38.756,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,0,100],"t":-11},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,64,100],"t":-1},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,64,100],"t":58},{"s":[100,0,100],"t":70}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[960,611.483,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[60.287,146.411],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-3.158,-34.45],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":15},{"ty":4,"nm":"bar3","sr":1,"st":-11,"op":70,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-3.158,38.756,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,0,100],"t":-3},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,87,100],"t":7},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,87,100],"t":58},{"s":[100,0,100],"t":70}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.29,"y":1},"s":[960,611.483,0],"t":-3,"ti":[-12,0,0],"to":[12,0,0]},{"s":[1032,611.483,0],"t":7}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[60.287,146.411],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-3.158,-34.45],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":16},{"ty":4,"nm":"bar2","sr":1,"st":-11,"op":70,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-3.158,38.756,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,0,100],"t":5},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,117,100],"t":15},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,117,100],"t":58},{"s":[100,0,100],"t":70}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.29,"y":1},"s":[1032,611.483,0],"t":5,"ti":[-12,0,0],"to":[12,0,0]},{"s":[1104,611.483,0],"t":15}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[60.287,146.411],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-3.158,-34.45],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":17},{"ty":4,"nm":"bar1","sr":1,"st":-11,"op":70,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[-3.158,38.756,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,0,100],"t":13},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,146,100],"t":23},{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[100,146,100],"t":58},{"s":[100,0,100],"t":70}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.29,"y":1},"s":[1104,611.483,0],"t":13,"ti":[-12,0,0],"to":[12,0,0]},{"s":[1176,611.483,0],"t":23}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Rectangle 1","ix":1,"cix":2,"np":3,"it":[{"ty":"rc","bm":0,"hd":false,"mn":"ADBE Vector Shape - Rect","nm":"Rectangle Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"r":{"a":0,"k":0,"ix":4},"s":{"a":0,"k":[60.287,146.411],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.4118,0.7882,0.8588],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[-3.158,-34.45],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":18},{"ty":0,"nm":"Pre-comp 2","sr":1,"st":70,"op":253,"ip":70,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[960,540,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[960,540,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"w":1920,"h":1080,"refId":"comp_27","ind":19}]},{"nm":"","id":"comp_26","layers":[{"ty":4,"nm":"dot 4","sr":1,"st":0,"op":300,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[345,-61,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[0,0,100],"t":139},{"s":[75,75,100],"t":154}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[1068.75,465,0],"t":150,"ti":[-19.5,10,0],"to":[19.5,-10,0]},{"s":[1185.75,405,0],"t":158}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Overshoot","ix":4,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Bounce","ix":5,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Friction","ix":6,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":60,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Ellipse 1","ix":1,"cix":2,"np":3,"it":[{"ty":"el","bm":0,"hd":false,"mn":"ADBE Vector Shape - Ellipse","nm":"Ellipse Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"s":{"a":0,"k":[52,52],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.4118,0.7882,0.8588],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[345,-61],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":1},{"ty":4,"nm":"dot 3","sr":1,"st":0,"op":300,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[345,-61,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[0,0,100],"t":136},{"s":[75,75,100],"t":151}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[1068.75,465,0],"t":147,"ti":[-6.16666650772095,-0.83333331346512,0],"to":[6.16666650772095,0.83333331346512,0]},{"s":[1105.75,470,0],"t":156}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Overshoot","ix":4,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Bounce","ix":5,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Friction","ix":6,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":60,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Ellipse 1","ix":1,"cix":2,"np":3,"it":[{"ty":"el","bm":0,"hd":false,"mn":"ADBE Vector Shape - Ellipse","nm":"Ellipse Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"s":{"a":0,"k":[52,52],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0.9647,0.898,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[345,-61],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":2},{"ty":4,"nm":"dot 2","sr":1,"st":0,"op":300,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[345,-61,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[0,0,100],"t":134},{"s":[75,75,100],"t":149}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[1068.75,465,0],"t":144,"ti":[7.33333349227905,1.83333337306976,0],"to":[-7.33333349227905,-1.83333337306976,0]},{"s":[1024.75,454,0],"t":153}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Overshoot","ix":4,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Bounce","ix":5,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Friction","ix":6,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":60,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Ellipse 1","ix":1,"cix":2,"np":3,"it":[{"ty":"el","bm":0,"hd":false,"mn":"ADBE Vector Shape - Ellipse","nm":"Ellipse Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"s":{"a":0,"k":[52,52],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[0,0,0],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[345,-61],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":3},{"ty":4,"nm":"dot","sr":1,"st":0,"op":300,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[345,-61,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[0,0,100],"t":132},{"s":[75,75,100],"t":147}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[1068.75,465,0],"t":141,"ti":[20.8333339691162,-8.16666698455811,0],"to":[-20.8333339691162,8.16666698455811,0]},{"s":[943.75,514,0],"t":150}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Scale - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Overshoot","ix":4,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":10,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Bounce","ix":5,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Position - Friction","ix":6,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":60,"ix":1}}]}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Ellipse 1","ix":1,"cix":2,"np":3,"it":[{"ty":"el","bm":0,"hd":false,"mn":"ADBE Vector Shape - Ellipse","nm":"Ellipse Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"s":{"a":0,"k":[52,52],"ix":2}},{"ty":"fl","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Fill","nm":"Fill 1","c":{"a":0,"k":[1,0.3098,0.6392],"ix":4},"r":1,"o":{"a":0,"k":100,"ix":5}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[345,-61],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]}],"ind":4},{"ty":4,"nm":"dash","sr":1,"st":0,"op":300,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":true,"ao":0,"ks":{"a":{"a":0,"k":[227,-135,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[1187,405,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"masksProperties":[{"nm":"Mask 1","inv":false,"mode":"s","x":{"a":0,"k":0,"ix":4},"o":{"a":0,"k":100,"ix":3},"pt":{"a":0,"k":{"c":true,"i":[[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]],"v":[[-31,-161],[-31,-13.08],[66,-91.08],[150,-68.08],[227,-135],[236.706,-191.084]]},"ix":1}}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":1,"cix":2,"np":2,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[0,0],[0,0]],"o":[[0,0],[0,0]],"v":[[227,-135],[227,69]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":5,"ix":5},"d":[{"nm":"dash","n":"d","v":{"a":0,"k":10,"ix":1}},{"nm":"offset","n":"o","v":{"a":0,"k":-14,"ix":7}}],"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.26,"y":1},"s":[0],"t":163},{"s":[98],"t":178}],"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":0,"k":0,"ix":1},"m":1},{"ty":"rp","bm":0,"hd":false,"mn":"ADBE Vector Filter - Repeater","nm":"Repeater 1","ix":3,"m":1,"c":{"a":0,"k":4,"ix":1},"o":{"a":0,"k":-3,"ix":2},"tr":{"a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0},"p":{"a":0,"k":[81,0],"ix":2},"r":{"a":0,"k":0,"ix":4},"sa":{"a":0,"k":0},"so":{"a":0,"k":100,"ix":5},"eo":{"a":0,"k":100,"ix":6}}}],"ind":5},{"ty":4,"nm":"graph2","sr":1,"st":0,"op":300,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":false,"ao":0,"ks":{"a":{"a":0,"k":[0,0,0],"ix":1},"s":{"a":0,"k":[100,100,100],"ix":6},"sk":{"a":0,"k":0},"p":{"a":0,"k":[960,540,0],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Shape 1","ix":1,"cix":2,"np":3,"it":[{"ty":"sh","bm":0,"hd":false,"mn":"ADBE Vector Shape - Group","nm":"Path 1","ix":1,"d":1,"ks":{"a":0,"k":{"c":false,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-16,-25.5],[57.5,-87],[152.5,-70],[227,-136.5]]},"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":9,"ix":5},"c":{"a":0,"k":[1,0.3098,0.6392],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[100,100],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[0,0],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.26,"y":1},"s":[0],"t":148},{"s":[100],"t":176}],"ix":2},"o":{"a":0,"k":0,"ix":3},"s":{"a":0,"k":0,"ix":1},"m":1}],"ind":6}]},{"nm":"","id":"comp_27","layers":[{"ty":4,"nm":"pie chart4","sr":1,"st":-81,"op":219,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":true,"ao":0,"ks":{"a":{"a":0,"k":[109,69.5,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.15,"y":1},"s":[100,100,100],"t":54},{"s":[0,0,100],"t":95}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[1069,609.5,0],"t":21,"ti":[0,24.1666660308838,0],"to":[0,-24.1666660308838,0]},{"s":[1069,464.5,0],"t":42}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"masksProperties":[{"nm":"Mask 1","inv":false,"mode":"a","x":{"a":0,"k":0,"ix":4},"o":{"a":0,"k":100,"ix":3},"pt":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-37,-81],[-37,71],[256,71],[256,-81]]}],"t":21},{"s":[{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-37,-81],[-36.583,225.959],[256.417,225.959],[256,-81]]}],"t":42}],"ix":1}}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Ellipse 1","ix":1,"cix":2,"np":3,"it":[{"ty":"el","bm":0,"hd":false,"mn":"ADBE Vector Shape - Ellipse","nm":"Ellipse Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"s":{"a":0,"k":[119,119],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":119,"ix":5},"c":{"a":0,"k":[1,0.3098,0.6392],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[113.278,113.278],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[109,69.5],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":0,"k":66,"ix":2},"o":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[0],"t":17},{"s":[28],"t":41}],"ix":3},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[75],"t":0},{"o":{"x":0.69,"y":0},"i":{"x":0.833,"y":1},"s":[80],"t":17},{"s":[88],"t":41}],"ix":1},"m":1}],"ind":1},{"ty":4,"nm":"pie chart3","sr":1,"st":-81,"op":219,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":true,"ao":0,"ks":{"a":{"a":0,"k":[109,69.5,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.15,"y":1},"s":[100,100,100],"t":54},{"s":[0,0,100],"t":95}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[1069,609.5,0],"t":21,"ti":[0,24.1666660308838,0],"to":[0,-24.1666660308838,0]},{"s":[1069,464.5,0],"t":42}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"masksProperties":[{"nm":"Mask 1","inv":false,"mode":"a","x":{"a":0,"k":0,"ix":4},"o":{"a":0,"k":100,"ix":3},"pt":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-37,-81],[-37,71],[256,71],[256,-81]]}],"t":21},{"s":[{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-37,-81],[-36.583,222.292],[256.417,222.292],[256,-81]]}],"t":42}],"ix":1}}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Ellipse 1","ix":1,"cix":2,"np":3,"it":[{"ty":"el","bm":0,"hd":false,"mn":"ADBE Vector Shape - Ellipse","nm":"Ellipse Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"s":{"a":0,"k":[119,119],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":119,"ix":5},"c":{"a":0,"k":[0,0,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[113.278,113.278],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[109,69.5],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":0,"k":66,"ix":2},"o":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[0],"t":17},{"s":[30],"t":41}],"ix":3},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[25],"t":0},{"o":{"x":0.69,"y":0},"i":{"x":0.833,"y":1},"s":[13],"t":17},{"s":[37],"t":41}],"ix":1},"m":1}],"ind":2},{"ty":4,"nm":"pie chart2","sr":1,"st":-81,"op":219,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":true,"ao":0,"ks":{"a":{"a":0,"k":[109,69.5,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.15,"y":1},"s":[100,100,100],"t":54},{"s":[0,0,100],"t":95}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[1069,609.5,0],"t":21,"ti":[0,24.1666660308838,0],"to":[0,-24.1666660308838,0]},{"s":[1069,464.5,0],"t":42}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"masksProperties":[{"nm":"Mask 1","inv":false,"mode":"a","x":{"a":0,"k":0,"ix":4},"o":{"a":0,"k":100,"ix":3},"pt":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-37,-81],[-37,71],[256,71],[256,-81]]}],"t":21},{"s":[{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-37,-81],[-36.292,213.289],[256.708,213.289],[256,-81]]}],"t":42}],"ix":1}}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Ellipse 1","ix":1,"cix":2,"np":3,"it":[{"ty":"el","bm":0,"hd":false,"mn":"ADBE Vector Shape - Ellipse","nm":"Ellipse Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"s":{"a":0,"k":[119,119],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":119,"ix":5},"c":{"a":0,"k":[0.9647,0.898,0],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[113.278,113.278],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[109,69.5],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":0,"k":66,"ix":2},"o":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[0],"t":17},{"s":[30],"t":41}],"ix":3},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[75],"t":0},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[100],"t":20},{"s":[100],"t":41}],"ix":1},"m":1}],"ind":3},{"ty":4,"nm":"pie chart1","sr":1,"st":-81,"op":219,"ip":0,"hd":false,"ddd":0,"bm":0,"hasMask":true,"ao":0,"ks":{"a":{"a":0,"k":[109,69.5,0],"ix":1},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.15,"y":1},"s":[100,100,100],"t":54},{"s":[0,0,100],"t":95}],"ix":6},"sk":{"a":0,"k":0},"p":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[1069,609.5,0],"t":21,"ti":[0,24.1666660308838,0],"to":[0,-24.1666660308838,0]},{"s":[1069,464.5,0],"t":42}],"ix":2},"r":{"a":0,"k":0,"ix":10},"sa":{"a":0,"k":0},"o":{"a":0,"k":100,"ix":11}},"ef":[{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Overshoot","ix":1,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":20,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Bounce","ix":2,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]},{"ty":0,"mn":"ADBE Slider Control","nm":"Offset - Trim Paths 1 - Friction","ix":3,"en":1,"ef":[{"ty":0,"mn":"ADBE Slider Control-0001","nm":"Slider","ix":1,"v":{"a":0,"k":40,"ix":1}}]}],"masksProperties":[{"nm":"Mask 1","inv":false,"mode":"a","x":{"a":0,"k":0,"ix":4},"o":{"a":0,"k":100,"ix":3},"pt":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-37,-81],[-37,71],[256,71],[256,-81]]}],"t":21},{"s":[{"c":true,"i":[[0,0],[0,0],[0,0],[0,0]],"o":[[0,0],[0,0],[0,0],[0,0]],"v":[[-37,-81],[-36.292,213.289],[256.708,213.289],[256,-81]]}],"t":42}],"ix":1}}],"shapes":[{"ty":"gr","bm":0,"hd":false,"mn":"ADBE Vector Group","nm":"Ellipse 1","ix":1,"cix":2,"np":3,"it":[{"ty":"el","bm":0,"hd":false,"mn":"ADBE Vector Shape - Ellipse","nm":"Ellipse Path 1","d":1,"p":{"a":0,"k":[0,0],"ix":3},"s":{"a":0,"k":[119,119],"ix":2}},{"ty":"st","bm":0,"hd":false,"mn":"ADBE Vector Graphic - Stroke","nm":"Stroke 1","lc":1,"lj":1,"ml":4,"o":{"a":0,"k":100,"ix":4},"w":{"a":0,"k":119,"ix":5},"c":{"a":0,"k":[0.4118,0.7882,0.8588],"ix":3}},{"ty":"tr","a":{"a":0,"k":[0,0],"ix":1},"s":{"a":0,"k":[113.278,113.278],"ix":3},"sk":{"a":0,"k":0,"ix":4},"p":{"a":0,"k":[109,69.5],"ix":2},"r":{"a":0,"k":0,"ix":6},"sa":{"a":0,"k":0,"ix":5},"o":{"a":0,"k":100,"ix":7}}]},{"ty":"tm","bm":0,"hd":false,"mn":"ADBE Vector Filter - Trim","nm":"Trim Paths 1","ix":2,"e":{"a":0,"k":66,"ix":2},"o":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.833,"y":0.833},"s":[0],"t":17},{"s":[29],"t":41}],"ix":3},"s":{"a":1,"k":[{"o":{"x":0.167,"y":0.167},"i":{"x":0.31,"y":1},"s":[25],"t":0},{"o":{"x":0.167,"y":0},"i":{"x":0.833,"y":1},"s":[0],"t":20},{"s":[0],"t":41}],"ix":1},"m":1}],"ind":4}]}]}';

function instance$8($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_tag_1 } = $$props;
	let { content_title_1 } = $$props;
	let { content_description_1a } = $$props;
	let { content_description_1b } = $$props;
	let { content_image_1 } = $$props;
	let { content_action_1 } = $$props;
	let { content_tag_2 } = $$props;
	let { content_title_2 } = $$props;
	let { content_description_2a } = $$props;
	let { content_description_2b } = $$props;
	let { content_description_2c } = $$props;
	let { content_description_2d } = $$props;
	let { content_image_2 } = $$props;
	let { content_action_2 } = $$props;
	let { checkmark } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(15, favicon = $$props.favicon);
		if ('content_tag_1' in $$props) $$invalidate(0, content_tag_1 = $$props.content_tag_1);
		if ('content_title_1' in $$props) $$invalidate(1, content_title_1 = $$props.content_title_1);
		if ('content_description_1a' in $$props) $$invalidate(2, content_description_1a = $$props.content_description_1a);
		if ('content_description_1b' in $$props) $$invalidate(3, content_description_1b = $$props.content_description_1b);
		if ('content_image_1' in $$props) $$invalidate(4, content_image_1 = $$props.content_image_1);
		if ('content_action_1' in $$props) $$invalidate(5, content_action_1 = $$props.content_action_1);
		if ('content_tag_2' in $$props) $$invalidate(6, content_tag_2 = $$props.content_tag_2);
		if ('content_title_2' in $$props) $$invalidate(7, content_title_2 = $$props.content_title_2);
		if ('content_description_2a' in $$props) $$invalidate(8, content_description_2a = $$props.content_description_2a);
		if ('content_description_2b' in $$props) $$invalidate(9, content_description_2b = $$props.content_description_2b);
		if ('content_description_2c' in $$props) $$invalidate(10, content_description_2c = $$props.content_description_2c);
		if ('content_description_2d' in $$props) $$invalidate(11, content_description_2d = $$props.content_description_2d);
		if ('content_image_2' in $$props) $$invalidate(12, content_image_2 = $$props.content_image_2);
		if ('content_action_2' in $$props) $$invalidate(13, content_action_2 = $$props.content_action_2);
		if ('checkmark' in $$props) $$invalidate(14, checkmark = $$props.checkmark);
	};

	return [
		content_tag_1,
		content_title_1,
		content_description_1a,
		content_description_1b,
		content_image_1,
		content_action_1,
		content_tag_2,
		content_title_2,
		content_description_2a,
		content_description_2b,
		content_description_2c,
		content_description_2d,
		content_image_2,
		content_action_2,
		checkmark,
		favicon
	];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$8, safe_not_equal, {
			favicon: 15,
			content_tag_1: 0,
			content_title_1: 1,
			content_description_1a: 2,
			content_description_1b: 3,
			content_image_1: 4,
			content_action_1: 5,
			content_tag_2: 6,
			content_title_2: 7,
			content_description_2a: 8,
			content_description_2b: 9,
			content_description_2c: 10,
			content_description_2d: 11,
			content_image_2: 12,
			content_action_2: 13,
			checkmark: 14
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$9(ctx) {
	let div12;
	let div11;
	let div10;
	let div7;
	let h3;
	let t0;
	let t1;
	let p0;
	let t2;
	let t3;
	let div6;
	let div5;
	let div0;
	let h60;
	let t4;
	let t5;
	let p1;
	let t6;
	let t7;
	let div1;
	let h61;
	let t8;
	let t9;
	let p2;
	let t10;
	let t11;
	let div2;
	let h62;
	let t12;
	let t13;
	let p3;
	let t14;
	let t15;
	let div3;
	let h63;
	let t16;
	let t17;
	let div4;
	let p4;
	let t18;
	let t19;
	let img0;
	let img0_src_value;
	let img0_alt_value;
	let t20;
	let img1;
	let img1_src_value;
	let img1_alt_value;
	let t21;
	let div9;
	let div8;
	let h4;
	let t22;
	let t23;
	let p5;
	let t24;

	return {
		c() {
			div12 = element("div");
			div11 = element("div");
			div10 = element("div");
			div7 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title*/ ctx[0]);
			t1 = space();
			p0 = element("p");
			t2 = text(/*content_description*/ ctx[1]);
			t3 = space();
			div6 = element("div");
			div5 = element("div");
			div0 = element("div");
			h60 = element("h6");
			t4 = text(/*content_tag_1*/ ctx[2]);
			t5 = space();
			p1 = element("p");
			t6 = text(/*content_paragraph_1*/ ctx[3]);
			t7 = space();
			div1 = element("div");
			h61 = element("h6");
			t8 = text(/*content_tag_2*/ ctx[4]);
			t9 = space();
			p2 = element("p");
			t10 = text(/*content_paragraph_2*/ ctx[5]);
			t11 = space();
			div2 = element("div");
			h62 = element("h6");
			t12 = text(/*content_tag_3*/ ctx[6]);
			t13 = space();
			p3 = element("p");
			t14 = text(/*content_paragraph_3*/ ctx[7]);
			t15 = space();
			div3 = element("div");
			h63 = element("h6");
			t16 = text(/*content_tag_4*/ ctx[8]);
			t17 = space();
			div4 = element("div");
			p4 = element("p");
			t18 = text(/*content_paragraph_4*/ ctx[9]);
			t19 = space();
			img0 = element("img");
			t20 = space();
			img1 = element("img");
			t21 = space();
			div9 = element("div");
			div8 = element("div");
			h4 = element("h4");
			t22 = text(/*bubble_title*/ ctx[11]);
			t23 = space();
			p5 = element("p");
			t24 = text(/*bubble_description*/ ctx[12]);
			this.h();
		},
		l(nodes) {
			div12 = claim_element(nodes, "DIV", { class: true, id: true });
			var div12_nodes = children(div12);
			div11 = claim_element(div12_nodes, "DIV", { class: true });
			var div11_nodes = children(div11);
			div10 = claim_element(div11_nodes, "DIV", { class: true });
			var div10_nodes = children(div10);
			div7 = claim_element(div10_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			h3 = claim_element(div7_nodes, "H3", {});
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div7_nodes);
			p0 = claim_element(div7_nodes, "P", { id: true, class: true });
			var p0_nodes = children(p0);
			t2 = claim_text(p0_nodes, /*content_description*/ ctx[1]);
			p0_nodes.forEach(detach);
			t3 = claim_space(div7_nodes);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", {});
			var div5_nodes = children(div5);
			div0 = claim_element(div5_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h60 = claim_element(div0_nodes, "H6", { class: true });
			var h60_nodes = children(h60);
			t4 = claim_text(h60_nodes, /*content_tag_1*/ ctx[2]);
			h60_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(div5_nodes);
			p1 = claim_element(div5_nodes, "P", { class: true });
			var p1_nodes = children(p1);
			t6 = claim_text(p1_nodes, /*content_paragraph_1*/ ctx[3]);
			p1_nodes.forEach(detach);
			t7 = claim_space(div5_nodes);
			div1 = claim_element(div5_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h61 = claim_element(div1_nodes, "H6", { class: true });
			var h61_nodes = children(h61);
			t8 = claim_text(h61_nodes, /*content_tag_2*/ ctx[4]);
			h61_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t9 = claim_space(div5_nodes);
			p2 = claim_element(div5_nodes, "P", { class: true });
			var p2_nodes = children(p2);
			t10 = claim_text(p2_nodes, /*content_paragraph_2*/ ctx[5]);
			p2_nodes.forEach(detach);
			t11 = claim_space(div5_nodes);
			div2 = claim_element(div5_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h62 = claim_element(div2_nodes, "H6", { class: true });
			var h62_nodes = children(h62);
			t12 = claim_text(h62_nodes, /*content_tag_3*/ ctx[6]);
			h62_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t13 = claim_space(div5_nodes);
			p3 = claim_element(div5_nodes, "P", { class: true });
			var p3_nodes = children(p3);
			t14 = claim_text(p3_nodes, /*content_paragraph_3*/ ctx[7]);
			p3_nodes.forEach(detach);
			t15 = claim_space(div5_nodes);
			div3 = claim_element(div5_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			h63 = claim_element(div3_nodes, "H6", { class: true });
			var h63_nodes = children(h63);
			t16 = claim_text(h63_nodes, /*content_tag_4*/ ctx[8]);
			h63_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t17 = claim_space(div5_nodes);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			p4 = claim_element(div4_nodes, "P", { class: true });
			var p4_nodes = children(p4);
			t18 = claim_text(p4_nodes, /*content_paragraph_4*/ ctx[9]);
			p4_nodes.forEach(detach);
			t19 = claim_space(div4_nodes);

			img0 = claim_element(div4_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			t20 = claim_space(div6_nodes);

			img1 = claim_element(div6_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			t21 = claim_space(div10_nodes);
			div9 = claim_element(div10_nodes, "DIV", { class: true });
			var div9_nodes = children(div9);
			div8 = claim_element(div9_nodes, "DIV", { class: true });
			var div8_nodes = children(div8);
			h4 = claim_element(div8_nodes, "H4", { class: true });
			var h4_nodes = children(h4);
			t22 = claim_text(h4_nodes, /*bubble_title*/ ctx[11]);
			h4_nodes.forEach(detach);
			t23 = claim_space(div8_nodes);
			p5 = claim_element(div8_nodes, "P", { class: true });
			var p5_nodes = children(p5);
			t24 = claim_text(p5_nodes, /*bubble_description*/ ctx[12]);
			p5_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			div9_nodes.forEach(detach);
			div10_nodes.forEach(detach);
			div11_nodes.forEach(detach);
			div12_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p0, "id", "content-paragraph-1");
			attr(p0, "class", "p-large svelte-sm90as");
			attr(h60, "class", "h700");
			attr(div0, "class", "tag-pink-large svelte-sm90as");
			attr(p1, "class", "p-medium");
			attr(h61, "class", "h700");
			attr(div1, "class", "tag-pink-large svelte-sm90as");
			attr(p2, "class", "p-medium");
			attr(h62, "class", "h700");
			attr(div2, "class", "tag-pink-large svelte-sm90as");
			attr(p3, "class", "p-medium");
			attr(h63, "class", "h700");
			attr(div3, "class", "tag-pink-large svelte-sm90as");
			attr(p4, "class", "p-medium");
			attr(img0, "id", "content-image-mobile");
			if (!src_url_equal(img0.src, img0_src_value = /*content_image*/ ctx[10].url)) attr(img0, "src", img0_src_value);
			attr(img0, "alt", img0_alt_value = /*content_image*/ ctx[10].alt);
			attr(img0, "class", "svelte-sm90as");
			attr(div4, "class", "final-content-column svelte-sm90as");
			attr(img1, "id", "content-image-desktop");
			if (!src_url_equal(img1.src, img1_src_value = /*content_image*/ ctx[10].url)) attr(img1, "src", img1_src_value);
			attr(img1, "alt", img1_alt_value = /*content_image*/ ctx[10].alt);
			attr(img1, "class", "svelte-sm90as");
			attr(div6, "class", "svelte-sm90as");
			attr(div7, "class", "section-container content svelte-sm90as");
			attr(h4, "class", "svelte-sm90as");
			attr(p5, "class", "p-medium svelte-sm90as");
			attr(div8, "class", "content-wrapper-2 svelte-sm90as");
			attr(div9, "class", "content-container-2 svelte-sm90as");
			attr(div10, "class", "wrapper svelte-sm90as");
			attr(div11, "class", "container svelte-sm90as");
			attr(div12, "class", "section");
			attr(div12, "id", "section-c200d1fc");
		},
		m(target, anchor) {
			insert_hydration(target, div12, anchor);
			append_hydration(div12, div11);
			append_hydration(div11, div10);
			append_hydration(div10, div7);
			append_hydration(div7, h3);
			append_hydration(h3, t0);
			append_hydration(div7, t1);
			append_hydration(div7, p0);
			append_hydration(p0, t2);
			append_hydration(div7, t3);
			append_hydration(div7, div6);
			append_hydration(div6, div5);
			append_hydration(div5, div0);
			append_hydration(div0, h60);
			append_hydration(h60, t4);
			append_hydration(div5, t5);
			append_hydration(div5, p1);
			append_hydration(p1, t6);
			append_hydration(div5, t7);
			append_hydration(div5, div1);
			append_hydration(div1, h61);
			append_hydration(h61, t8);
			append_hydration(div5, t9);
			append_hydration(div5, p2);
			append_hydration(p2, t10);
			append_hydration(div5, t11);
			append_hydration(div5, div2);
			append_hydration(div2, h62);
			append_hydration(h62, t12);
			append_hydration(div5, t13);
			append_hydration(div5, p3);
			append_hydration(p3, t14);
			append_hydration(div5, t15);
			append_hydration(div5, div3);
			append_hydration(div3, h63);
			append_hydration(h63, t16);
			append_hydration(div5, t17);
			append_hydration(div5, div4);
			append_hydration(div4, p4);
			append_hydration(p4, t18);
			append_hydration(div4, t19);
			append_hydration(div4, img0);
			append_hydration(div6, t20);
			append_hydration(div6, img1);
			append_hydration(div10, t21);
			append_hydration(div10, div9);
			append_hydration(div9, div8);
			append_hydration(div8, h4);
			append_hydration(h4, t22);
			append_hydration(div8, t23);
			append_hydration(div8, p5);
			append_hydration(p5, t24);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title*/ 1) set_data(t0, /*content_title*/ ctx[0]);
			if (dirty & /*content_description*/ 2) set_data(t2, /*content_description*/ ctx[1]);
			if (dirty & /*content_tag_1*/ 4) set_data(t4, /*content_tag_1*/ ctx[2]);
			if (dirty & /*content_paragraph_1*/ 8) set_data(t6, /*content_paragraph_1*/ ctx[3]);
			if (dirty & /*content_tag_2*/ 16) set_data(t8, /*content_tag_2*/ ctx[4]);
			if (dirty & /*content_paragraph_2*/ 32) set_data(t10, /*content_paragraph_2*/ ctx[5]);
			if (dirty & /*content_tag_3*/ 64) set_data(t12, /*content_tag_3*/ ctx[6]);
			if (dirty & /*content_paragraph_3*/ 128) set_data(t14, /*content_paragraph_3*/ ctx[7]);
			if (dirty & /*content_tag_4*/ 256) set_data(t16, /*content_tag_4*/ ctx[8]);
			if (dirty & /*content_paragraph_4*/ 512) set_data(t18, /*content_paragraph_4*/ ctx[9]);

			if (dirty & /*content_image*/ 1024 && !src_url_equal(img0.src, img0_src_value = /*content_image*/ ctx[10].url)) {
				attr(img0, "src", img0_src_value);
			}

			if (dirty & /*content_image*/ 1024 && img0_alt_value !== (img0_alt_value = /*content_image*/ ctx[10].alt)) {
				attr(img0, "alt", img0_alt_value);
			}

			if (dirty & /*content_image*/ 1024 && !src_url_equal(img1.src, img1_src_value = /*content_image*/ ctx[10].url)) {
				attr(img1, "src", img1_src_value);
			}

			if (dirty & /*content_image*/ 1024 && img1_alt_value !== (img1_alt_value = /*content_image*/ ctx[10].alt)) {
				attr(img1, "alt", img1_alt_value);
			}

			if (dirty & /*bubble_title*/ 2048) set_data(t22, /*bubble_title*/ ctx[11]);
			if (dirty & /*bubble_description*/ 4096) set_data(t24, /*bubble_description*/ ctx[12]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div12);
		}
	};
}

function instance$9($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_description } = $$props;
	let { content_tag_1 } = $$props;
	let { content_paragraph_1 } = $$props;
	let { content_tag_2 } = $$props;
	let { content_paragraph_2 } = $$props;
	let { content_tag_3 } = $$props;
	let { content_paragraph_3 } = $$props;
	let { content_tag_4 } = $$props;
	let { content_paragraph_4 } = $$props;
	let { content_image } = $$props;
	let { bubble_title } = $$props;
	let { bubble_description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(13, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_description' in $$props) $$invalidate(1, content_description = $$props.content_description);
		if ('content_tag_1' in $$props) $$invalidate(2, content_tag_1 = $$props.content_tag_1);
		if ('content_paragraph_1' in $$props) $$invalidate(3, content_paragraph_1 = $$props.content_paragraph_1);
		if ('content_tag_2' in $$props) $$invalidate(4, content_tag_2 = $$props.content_tag_2);
		if ('content_paragraph_2' in $$props) $$invalidate(5, content_paragraph_2 = $$props.content_paragraph_2);
		if ('content_tag_3' in $$props) $$invalidate(6, content_tag_3 = $$props.content_tag_3);
		if ('content_paragraph_3' in $$props) $$invalidate(7, content_paragraph_3 = $$props.content_paragraph_3);
		if ('content_tag_4' in $$props) $$invalidate(8, content_tag_4 = $$props.content_tag_4);
		if ('content_paragraph_4' in $$props) $$invalidate(9, content_paragraph_4 = $$props.content_paragraph_4);
		if ('content_image' in $$props) $$invalidate(10, content_image = $$props.content_image);
		if ('bubble_title' in $$props) $$invalidate(11, bubble_title = $$props.bubble_title);
		if ('bubble_description' in $$props) $$invalidate(12, bubble_description = $$props.bubble_description);
	};

	return [
		content_title,
		content_description,
		content_tag_1,
		content_paragraph_1,
		content_tag_2,
		content_paragraph_2,
		content_tag_3,
		content_paragraph_3,
		content_tag_4,
		content_paragraph_4,
		content_image,
		bubble_title,
		bubble_description,
		favicon
	];
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$9, create_fragment$9, safe_not_equal, {
			favicon: 13,
			content_title: 0,
			content_description: 1,
			content_tag_1: 2,
			content_paragraph_1: 3,
			content_tag_2: 4,
			content_paragraph_2: 5,
			content_tag_3: 6,
			content_paragraph_3: 7,
			content_tag_4: 8,
			content_paragraph_4: 9,
			content_image: 10,
			bubble_title: 11,
			bubble_description: 12
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[12] = list[i].link;
	child_ctx[13] = list[i].icon;
	return child_ctx;
}

// (424:8) {#each social as { link, icon }}
function create_each_block$3(ctx) {
	let a;
	let span;
	let icon;
	let t;
	let a_href_value;
	let a_alt_value;
	let current;

	icon = new Component$1({
			props: {
				style: "width: 40px; height: 40px;",
				icon: /*icon*/ ctx[13]
			}
		});

	return {
		c() {
			a = element("a");
			span = element("span");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, alt: true });
			var a_nodes = children(a);
			span = claim_element(a_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			claim_component(icon.$$.fragment, span_nodes);
			span_nodes.forEach(detach);
			t = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "icon svelte-2u5228");
			attr(a, "href", a_href_value = /*link*/ ctx[12].url);
			attr(a, "alt", a_alt_value = /*link*/ ctx[12].alt);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, span);
			mount_component(icon, span, null);
			append_hydration(a, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 64) icon_changes.icon = /*icon*/ ctx[13];
			icon.$set(icon_changes);

			if (!current || dirty & /*social*/ 64 && a_href_value !== (a_href_value = /*link*/ ctx[12].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*social*/ 64 && a_alt_value !== (a_alt_value = /*link*/ ctx[12].alt)) {
				attr(a, "alt", a_alt_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

function create_fragment$a(ctx) {
	let div7;
	let div6;
	let div5;
	let div4;
	let h3;
	let t0;
	let t1;
	let p0;
	let t2;
	let t3;
	let p1;
	let t4;
	let t5;
	let form;
	let iframe;
	let iframe_src_value;
	let t6;
	let div2;
	let div0;
	let p2;
	let t7;
	let t8;
	let div1;
	let p3;
	let t9;
	let t10;
	let p4;
	let t11;
	let t12;
	let div3;
	let current;
	let each_value = /*social*/ ctx[6];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$3(get_each_context$3(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div7 = element("div");
			div6 = element("div");
			div5 = element("div");
			div4 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title*/ ctx[0]);
			t1 = space();
			p0 = element("p");
			t2 = text(/*content_paragraph_1*/ ctx[1]);
			t3 = space();
			p1 = element("p");
			t4 = text(/*content_paragraph_2*/ ctx[2]);
			t5 = space();
			form = element("form");
			iframe = element("iframe");
			t6 = space();
			div2 = element("div");
			div0 = element("div");
			p2 = element("p");
			t7 = text(/*content_bubble_1*/ ctx[4]);
			t8 = space();
			div1 = element("div");
			p3 = element("p");
			t9 = text(/*content_bubble_2*/ ctx[5]);
			t10 = space();
			p4 = element("p");
			t11 = text(/*content_paragraph_3*/ ctx[3]);
			t12 = space();
			div3 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div7 = claim_element(nodes, "DIV", { class: true, id: true });
			var div7_nodes = children(div7);
			div6 = claim_element(div7_nodes, "DIV", { class: true, id: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			h3 = claim_element(div4_nodes, "H3", {});
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div4_nodes);
			p0 = claim_element(div4_nodes, "P", { class: true });
			var p0_nodes = children(p0);
			t2 = claim_text(p0_nodes, /*content_paragraph_1*/ ctx[1]);
			p0_nodes.forEach(detach);
			t3 = claim_space(div4_nodes);
			p1 = claim_element(div4_nodes, "P", { class: true });
			var p1_nodes = children(p1);
			t4 = claim_text(p1_nodes, /*content_paragraph_2*/ ctx[2]);
			p1_nodes.forEach(detach);
			t5 = claim_space(div4_nodes);
			form = claim_element(div4_nodes, "FORM", { class: true });
			var form_nodes = children(form);
			iframe = claim_element(form_nodes, "IFRAME", { src: true, title: true, class: true });
			children(iframe).forEach(detach);
			form_nodes.forEach(detach);
			t6 = claim_space(div4_nodes);
			div2 = claim_element(div4_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			p2 = claim_element(div0_nodes, "P", { class: true });
			var p2_nodes = children(p2);
			t7 = claim_text(p2_nodes, /*content_bubble_1*/ ctx[4]);
			p2_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t8 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			p3 = claim_element(div1_nodes, "P", { class: true });
			var p3_nodes = children(p3);
			t9 = claim_text(p3_nodes, /*content_bubble_2*/ ctx[5]);
			p3_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t10 = claim_space(div4_nodes);
			p4 = claim_element(div4_nodes, "P", { class: true });
			var p4_nodes = children(p4);
			t11 = claim_text(p4_nodes, /*content_paragraph_3*/ ctx[3]);
			p4_nodes.forEach(detach);
			t12 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div3_nodes);
			}

			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p0, "class", "p-large svelte-2u5228");
			attr(p1, "class", "p-large svelte-2u5228");
			if (!src_url_equal(iframe.src, iframe_src_value = "https://cdn.forms-content.sg-form.com/a0bf2821-1221-11ee-b804-2a098f035ca4")) attr(iframe, "src", iframe_src_value);
			attr(iframe, "title", "contact form");
			attr(iframe, "class", "svelte-2u5228");
			attr(form, "class", "svelte-2u5228");
			attr(p2, "class", "p-medium svelte-2u5228");
			attr(div0, "class", "bubble-1 svelte-2u5228");
			attr(p3, "class", "p-medium svelte-2u5228");
			attr(div1, "class", "bubble-2 svelte-2u5228");
			attr(div2, "class", "bubbles svelte-2u5228");
			attr(p4, "class", "p-large svelte-2u5228");
			attr(div3, "class", "social-links svelte-2u5228");
			attr(div4, "class", "section-container content svelte-2u5228");
			attr(div5, "class", "wrapper svelte-2u5228");
			attr(div6, "class", "container svelte-2u5228");
			attr(div6, "id", "contact-us");
			attr(div7, "class", "section");
			attr(div7, "id", "section-30f9677d");
		},
		m(target, anchor) {
			insert_hydration(target, div7, anchor);
			append_hydration(div7, div6);
			append_hydration(div6, div5);
			append_hydration(div5, div4);
			append_hydration(div4, h3);
			append_hydration(h3, t0);
			append_hydration(div4, t1);
			append_hydration(div4, p0);
			append_hydration(p0, t2);
			append_hydration(div4, t3);
			append_hydration(div4, p1);
			append_hydration(p1, t4);
			append_hydration(div4, t5);
			append_hydration(div4, form);
			append_hydration(form, iframe);
			append_hydration(div4, t6);
			append_hydration(div4, div2);
			append_hydration(div2, div0);
			append_hydration(div0, p2);
			append_hydration(p2, t7);
			append_hydration(div2, t8);
			append_hydration(div2, div1);
			append_hydration(div1, p3);
			append_hydration(p3, t9);
			append_hydration(div4, t10);
			append_hydration(div4, p4);
			append_hydration(p4, t11);
			append_hydration(div4, t12);
			append_hydration(div4, div3);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div3, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*content_title*/ 1) set_data(t0, /*content_title*/ ctx[0]);
			if (!current || dirty & /*content_paragraph_1*/ 2) set_data(t2, /*content_paragraph_1*/ ctx[1]);
			if (!current || dirty & /*content_paragraph_2*/ 4) set_data(t4, /*content_paragraph_2*/ ctx[2]);
			if (!current || dirty & /*content_bubble_1*/ 16) set_data(t7, /*content_bubble_1*/ ctx[4]);
			if (!current || dirty & /*content_bubble_2*/ 32) set_data(t9, /*content_bubble_2*/ ctx[5]);
			if (!current || dirty & /*content_paragraph_3*/ 8) set_data(t11, /*content_paragraph_3*/ ctx[3]);

			if (dirty & /*social*/ 64) {
				each_value = /*social*/ ctx[6];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$3(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$3(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div3, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div7);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$a($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_paragraph_1 } = $$props;
	let { content_paragraph_2 } = $$props;
	let { content_paragraph_3 } = $$props;
	let { content_bubble_1 } = $$props;
	let { content_bubble_2 } = $$props;
	let { inputs } = $$props;
	let { submit_label } = $$props;
	let { social } = $$props;
	let { form_success_title } = $$props;
	let { form_success_description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(7, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_paragraph_1' in $$props) $$invalidate(1, content_paragraph_1 = $$props.content_paragraph_1);
		if ('content_paragraph_2' in $$props) $$invalidate(2, content_paragraph_2 = $$props.content_paragraph_2);
		if ('content_paragraph_3' in $$props) $$invalidate(3, content_paragraph_3 = $$props.content_paragraph_3);
		if ('content_bubble_1' in $$props) $$invalidate(4, content_bubble_1 = $$props.content_bubble_1);
		if ('content_bubble_2' in $$props) $$invalidate(5, content_bubble_2 = $$props.content_bubble_2);
		if ('inputs' in $$props) $$invalidate(8, inputs = $$props.inputs);
		if ('submit_label' in $$props) $$invalidate(9, submit_label = $$props.submit_label);
		if ('social' in $$props) $$invalidate(6, social = $$props.social);
		if ('form_success_title' in $$props) $$invalidate(10, form_success_title = $$props.form_success_title);
		if ('form_success_description' in $$props) $$invalidate(11, form_success_description = $$props.form_success_description);
	};

	return [
		content_title,
		content_paragraph_1,
		content_paragraph_2,
		content_paragraph_3,
		content_bubble_1,
		content_bubble_2,
		social,
		favicon,
		inputs,
		submit_label,
		form_success_title,
		form_success_description
	];
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$a, create_fragment$a, safe_not_equal, {
			favicon: 7,
			content_title: 0,
			content_paragraph_1: 1,
			content_paragraph_2: 2,
			content_paragraph_3: 3,
			content_bubble_1: 4,
			content_bubble_2: 5,
			inputs: 8,
			submit_label: 9,
			social: 6,
			form_success_title: 10,
			form_success_description: 11
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$4(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	return child_ctx;
}

// (70:4) {#each nav as { link }}
function create_each_block$4(ctx) {
	let h6;
	let a;
	let t0_value = /*link*/ ctx[3].label + "";
	let t0;
	let a_target_value;
	let a_href_value;
	let t1;

	return {
		c() {
			h6 = element("h6");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			h6 = claim_element(nodes, "H6", { id: true, class: true });
			var h6_nodes = children(h6);
			a = claim_element(h6_nodes, "A", { target: true, class: true, href: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(h6_nodes);
			h6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "target", a_target_value = /*link*/ ctx[3].label.includes('Whitepaper')
			? '_blank'
			: '_self');

			attr(a, "class", "link svelte-14fdjq7");
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(h6, "id", "links");
			attr(h6, "class", "h950 svelte-14fdjq7");
		},
		m(target, anchor) {
			insert_hydration(target, h6, anchor);
			append_hydration(h6, a);
			append_hydration(a, t0);
			append_hydration(h6, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 1 && t0_value !== (t0_value = /*link*/ ctx[3].label + "")) set_data(t0, t0_value);

			if (dirty & /*nav*/ 1 && a_target_value !== (a_target_value = /*link*/ ctx[3].label.includes('Whitepaper')
			? '_blank'
			: '_self')) {
				attr(a, "target", a_target_value);
			}

			if (dirty & /*nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(h6);
		}
	};
}

function create_fragment$b(ctx) {
	let div;
	let footer;
	let nav_1;
	let t0;
	let span;
	let p;
	let t1;
	let each_value = /*nav*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$4(get_each_context$4(ctx, each_value, i));
	}

	return {
		c() {
			div = element("div");
			footer = element("footer");
			nav_1 = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			span = element("span");
			p = element("p");
			t1 = text(/*copyright*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			footer = claim_element(div_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			nav_1 = claim_element(footer_nodes, "NAV", { class: true });
			var nav_1_nodes = children(nav_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_1_nodes);
			}

			nav_1_nodes.forEach(detach);
			t0 = claim_space(footer_nodes);
			span = claim_element(footer_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			p = claim_element(span_nodes, "P", { id: true, class: true });
			var p_nodes = children(p);
			t1 = claim_text(p_nodes, /*copyright*/ ctx[1]);
			p_nodes.forEach(detach);
			span_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav_1, "class", "svelte-14fdjq7");
			attr(p, "id", "copyright");
			attr(p, "class", "p-small svelte-14fdjq7");
			attr(span, "class", "svelte-14fdjq7");
			attr(footer, "class", "section-container svelte-14fdjq7");
			attr(div, "class", "section");
			attr(div, "id", "section-a861bb52");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, footer);
			append_hydration(footer, nav_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav_1, null);
				}
			}

			append_hydration(footer, t0);
			append_hydration(footer, span);
			append_hydration(span, p);
			append_hydration(p, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*nav*/ 1) {
				each_value = /*nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$4(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$4(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav_1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*copyright*/ 2) set_data(t1, /*copyright*/ ctx[1]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$b($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { nav } = $$props;
	let { copyright } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('nav' in $$props) $$invalidate(0, nav = $$props.nav);
		if ('copyright' in $$props) $$invalidate(1, copyright = $$props.copyright);
	};

	return [nav, copyright, favicon];
}

class Component$b extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$b, create_fragment$b, safe_not_equal, { favicon: 2, nav: 0, copyright: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function instance$c($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component$c extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$c, null, safe_not_equal, { favicon: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$c(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let t7;
	let component_8;
	let t8;
	let component_9;
	let t9;
	let component_10;
	let t10;
	let component_11;
	let current;

	component_0 = new Component({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				}
			}
		});

	component_1 = new Component$2({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				logo: {
					"image": {
						"alt": "logo",
						"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778unlok-logo2%20copy.svg",
						"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778unlok-logo2%20copy.svg",
						"size": 3
					},
					"title": ""
				},
				site_nav: [
					{
						"link": { "url": "/personal", "label": "Personal" }
					},
					{
						"link": {
							"url": "/business",
							"label": "Business",
							"active": false
						}
					},
					{
						"link": { "url": "/investor", "label": "Investor" }
					}
				],
				site_nav_button: { "url": "/portal", "label": "Get Started" }
			}
		});

	component_2 = new Component$3({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				background: {
					"alt": "background image",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686873919000home-banner-bg-large.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686873919000home-banner-bg-large.svg",
					"size": 40
				},
				logo: {
					"image": {
						"alt": "logo",
						"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778Subtract.svg",
						"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686165013778Subtract.svg",
						"size": 1
					},
					"title": ""
				},
				site_nav: [
					{
						"link": { "url": "/personal", "label": "Personal" }
					},
					{
						"link": {
							"url": "/business",
							"label": "Business",
							"active": false
						}
					},
					{
						"link": { "url": "/team", "label": "Investor" }
					}
				],
				site_nav_button: "Get Started",
				hero_title1: "Unlock the Future",
				hero_title2: "of Loyalty Rewards",
				hero_description: "Unleash the Power of Blockchain Rewards",
				hero_feature: [{ "title": "Earn" }, { "title": "Redeem" }, { "title": "Repeat" }],
				hero_image: {
					"alt": "Hero Image",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686084660000home-banner.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686084660000home-banner.png",
					"size": 124
				},
				home_banner_mobile: {
					"alt": "Home Banner Mobile",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687544314000home%20banner-768-pink-piece.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687544314000home%20banner-768-pink-piece.svg",
					"size": 0
				},
				home_banner_small_desktop: {
					"alt": "Home Banner Small Desktop",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687544473000home%20banner-1024-pink-piece.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687544473000home%20banner-1024-pink-piece.svg",
					"size": 0
				}
			}
		});

	component_3 = new Component$4({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title: "Welcome to UNLOK, where loyalty rewards take on a whole new dimension.",
				content_paragraph_1: "Prepare to embark on a journey that is revolutionizing the industry and redefining how brands connect with their customers. Experience a platform that shapes the future of loyalty and maximizes returns",
				content_paragraph_2: "UNLOK harnesses the power of blockchain technology, creating an unrivalled decentralized ecosystem. Say goodbye to limitations and welcome a world of boundless possibilities as we enable the seamless exchange and redemption of loyalty points within a single platform. Users earn UNLOK tokens with every transaction, unlocking a treasure trove of personalized rewards that cater to their unique preferences and lifestyle.",
				action_button: {
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/Whitepaper.pdf?t=2023-06-23T23%3A35%3A42.985Z",
					"label": "White Paper"
				}
			}
		});

	component_4 = new Component$5({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title: "Revolutionize Your Loyalty Rewards Program",
				content_paragraph_1: "We’re revolutionizing the way merchants engage with their customers through loyalty rewards, allowing you to take advantage of our innovative solutions to drive customer loyalty, expand your customer base, and boost your revenue, creating a seamless and rewarding experience for your customers, unlocking the limitless potential for your business.",
				content_image_desktop: {
					"alt": "Revolutionize Rewards",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003893000revolutionize-rewards-desktop%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003893000revolutionize-rewards-desktop%20copy.svg",
					"size": 41
				},
				content_image_mobile: {
					"alt": "Revolutionize Rewards",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003946000revolutionize-rewards-mobile%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003946000revolutionize-rewards-mobile%20copy.svg",
					"size": 43
				},
				action_button: {
					"url": "/business",
					"label": "Learn More"
				}
			}
		});

	component_5 = new Component$6({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title: "Join the UNLOK Community and Get Rewarded",
				content_paragraph_1: "Get ready to embark on an exciting journey of rewards and adventure with UNLOK. Our innovative platform is designed to bring joy and excitement to your everyday life. Earn UNLOK tokens, unlock exclusive perks, and explore a world of possibilities.",
				action_button: {
					"url": "/personal",
					"label": "Discover Unlok Rewards"
				}
			}
		});

	component_6 = new Component$7({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_tag: "Going Beyond Rewards",
				content_title: "The Unlok Ecosystem",
				content_paragraph_1: "At UNLOK, we believe in offering more than just traditional rewards. Our platform encompasses a comprehensive ecosystem that empowers merchants and consumers to explore new horizons and unlock a world of possibilities. Discover the diverse components of our ecosystem:",
				content_card: [
					{
						"image": {
							"alt": "UnlokPay",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686002968000UnlokPay%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686002968000UnlokPay%20copy.svg",
							"size": 14
						},
						"title": "UnlokPay",
						"description": "Bid farewell to transaction charges and embrace hassle-free payments with our pioneering payment facilitator service."
					},
					{
						"image": {
							"alt": "UnlokMarket",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003002000UnlokMarket%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003002000UnlokMarket%20copy.svg",
							"size": 6
						},
						"title": "UnlokMarket",
						"description": "Immerse yourself in our open-market e-commerce platform, where cryptocurrencies unlock a world of exclusive NFTs and tailored experiences."
					},
					{
						"image": {
							"alt": "UnlokGC",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003079000UnlokGC%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003079000UnlokGC%20copy.svg",
							"size": 7
						},
						"title": "UnlokGC",
						"description": "Instantly exchange UNLOK tokens for international gift cards, unlocking discounts at popular retailers, electronics outlets, and restaurants."
					},
					{
						"image": {
							"alt": "UnlokDebit",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003097000UnlokDebit%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003097000UnlokDebit%20copy.svg",
							"size": 5
						},
						"title": "UnlokDebit",
						"description": "Streamline your transactions with our secure debit card, merging UNLOK tokens and other cryptocurrencies for convenient global acceptance."
					},
					{
						"image": {
							"alt": "UnlokReward",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686760072000unlokreward.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686760072000unlokreward.svg",
							"size": 9
						},
						"title": "UnlokReward",
						"description": "Holding UNLOK tokens opens the door to passive rewards, including discounted airfare, hotel stays, online shop vouchers, and exclusive NFTs, making your journey truly rewarding."
					}
				]
			}
		});

	component_7 = new Component$8({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_tag_1: "Staking at UNLOK",
				content_title_1: "Unlocking High Stakes and High Rewards",
				content_description_1a: "At UNLOK, we believe in empowering our users with flexibility, autonomy, and rewarding opportunities through our staking mechanism. Staking UNLOK tokens allow you to earn passive rewards and give you complete control over your staking preferences.",
				content_description_1b: "Discover how staking UNLOK tokens can unlock a world of possibilities. Learn more about our staking mechanism and the benefits it offers. Start earning passive rewards today!",
				content_image_1: {
					"alt": "Staking",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686607722000Staking1%20copy%202.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686607722000Staking1%20copy%202.svg",
					"size": 45
				},
				content_action_1: {
					"url": "/personal",
					"label": "Maximize Your Rewards"
				},
				content_tag_2: "UNLOK Tokenomics",
				content_title_2: "Powering the Future of Blockchain Rewards",
				content_description_2a: "Discover the power of UNLOK tokenomics and how it drives our innovative blockchain rewards platform. At UNLOK, we have carefully designed our token allocation to ensure seamless ecosystem functioning and long-term success.",
				content_description_2b: "Strategically structured to fuel the growth and functionality of the UNLOK ecosystem.",
				content_description_2c: "Flexibility and adaptability are built into our tokenomics, ensuring we can meet future needs and respond to unforeseen circumstances.",
				content_description_2d: "Discover the full potential of UNLOK's tokenomics and how they can benefit you. Dive deeper into our innovative blockchain rewards platform and explore the exciting opportunities that await. ",
				content_image_2: {
					"alt": "Chart",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1685746107000screen-shapes%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1685746107000screen-shapes%20copy.svg",
					"size": 1
				},
				content_action_2: {
					"url": "/tokenomics",
					"label": "Learn about tokenomics"
				},
				checkmark: {
					"alt": "Checkmark",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686275060586check-square%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686275060586check-square%20copy.svg",
					"size": 1
				}
			}
		});

	component_8 = new Component$9({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title: "Team",
				content_description: "At UNLOK, our team consists of industry leaders, pioneers, and passionate individuals driving the future of loyalty rewards. With diverse expertise and a shared vision for innovation, we are revolutionizing the industry. Get to know the extraordinary individuals behind UNLOK:",
				content_tag_1: "Innovators and Trailblazers",
				content_paragraph_1: "Fearlessly challenging the status quo, our team constantly seeks new opportunities and pushes boundaries in loyalty rewards.",
				content_tag_2: "Collaborative Team Players",
				content_paragraph_2: "Foster a collaborative environment where ideas are shared, valued perspectives, and collective strengths are leveraged.",
				content_tag_3: "Industry Experts",
				content_paragraph_3: "Seasoned professionals with deep knowledge of loyalty programs, blockchain technology, and financial services, setting new industry standards.",
				content_tag_4: "Passion and Dedication",
				content_paragraph_4: "Driven by unwavering commitment, our team's dedication ensures every aspect of UNLOK exceeds expectations.",
				content_image: {
					"alt": "Team",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686084672000team-img.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686084672000team-img.png",
					"size": 105
				},
				bubble_title: "Join Our Team",
				bubble_description: "Are you a visionary, trailblazer, or industry expert passionate about shaping the future of loyalty rewards? Explore career opportunities at UNLOK and be part of our journey to redefine the industry. Together, we unlock endless possibilities."
			}
		});

	component_9 = new Component$a({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				content_title: "Contact Us",
				content_paragraph_1: "We'd love to hear from you! Whether you have questions, partnership inquiries, or just want to share your excitement, our team is here to assist you.  ",
				content_paragraph_2: "Get in touch with us using the contact details below:",
				content_paragraph_3: "Connect with us on social media for the latest updates, thrilling announcements, and an extra dose of excitement:",
				content_bubble_1: "Our team is available to respond to your emails promptly and provide the information you need.",
				content_bubble_2: "We look forward to connecting with you and sharing the exhilarating world of UNLOK! Get ready to unlock the future of loyalty rewards and embark on an adventure like no other.",
				inputs: [
					{
						"type": "text",
						"label": "Name",
						"endpoint": "https://getform.io/f/d6b0d018-5bc1-4e0b-bc88-7d4704922274",
						"placeholder": "Name"
					},
					{
						"type": "email",
						"label": "Email",
						"endpoint": "https://getform.io/f/d6b0d018-5bc1-4e0b-bc88-7d4704922274",
						"placeholder": "Email"
					},
					{
						"type": "textarea",
						"label": "Textarea",
						"endpoint": "",
						"placeholder": "Textarea"
					}
				],
				submit_label: "Send Message",
				social: [
					{
						"icon": "fa-brands:twitter-square",
						"link": { "url": "/", "label": "Twitter" }
					},
					{
						"icon": "fa6-brands:linkedin",
						"link": { "url": "/", "label": "Linkedin" }
					},
					{
						"icon": "fa-brands:facebook-square",
						"link": { "url": "/", "label": "Facebook" }
					}
				],
				form_success_title: "Thank you for contacting us!",
				form_success_description: "We'll be in touch shortly"
			}
		});

	component_10 = new Component$b({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				},
				nav: [
					{
						"link": {
							"url": "/tokenomics",
							"label": "Tokenomics"
						}
					},
					{
						"link": {
							"url": "/privacy",
							"label": "Privacy Policy"
						}
					},
					{
						"link": {
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/Whitepaper.pdf?t=2023-06-23T23%3A35%3A42.985Z",
							"label": "Whitepaper"
						}
					},
					{
						"link": {
							"url": "https://unlokloyalty.com#contact-us",
							"label": "Contact Us"
						}
					}
				],
				copyright: "© 2023 UNLOK. All rights reserved."
			}
		});

	component_11 = new Component$c({
			props: {
				favicon: {
					"alt": "Unlok favicon",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687548555125UNLOK%20-%20Transparent%20Icon_FINAL.png",
					"size": 23
				}
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
			t7 = space();
			create_component(component_8.$$.fragment);
			t8 = space();
			create_component(component_9.$$.fragment);
			t9 = space();
			create_component(component_10.$$.fragment);
			t10 = space();
			create_component(component_11.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
			t7 = claim_space(nodes);
			claim_component(component_8.$$.fragment, nodes);
			t8 = claim_space(nodes);
			claim_component(component_9.$$.fragment, nodes);
			t9 = claim_space(nodes);
			claim_component(component_10.$$.fragment, nodes);
			t10 = claim_space(nodes);
			claim_component(component_11.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			insert_hydration(target, t7, anchor);
			mount_component(component_8, target, anchor);
			insert_hydration(target, t8, anchor);
			mount_component(component_9, target, anchor);
			insert_hydration(target, t9, anchor);
			mount_component(component_10, target, anchor);
			insert_hydration(target, t10, anchor);
			mount_component(component_11, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			transition_in(component_8.$$.fragment, local);
			transition_in(component_9.$$.fragment, local);
			transition_in(component_10.$$.fragment, local);
			transition_in(component_11.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			transition_out(component_8.$$.fragment, local);
			transition_out(component_9.$$.fragment, local);
			transition_out(component_10.$$.fragment, local);
			transition_out(component_11.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
			if (detaching) detach(t7);
			destroy_component(component_8, detaching);
			if (detaching) detach(t8);
			destroy_component(component_9, detaching);
			if (detaching) detach(t9);
			destroy_component(component_10, detaching);
			if (detaching) detach(t10);
			destroy_component(component_11, detaching);
		}
	};
}

class Component$d extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$c, safe_not_equal, {});
	}
}

export default Component$d;
