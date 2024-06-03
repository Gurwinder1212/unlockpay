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
			const head_nodes = head_selector('svelte-dx79v6', document.head);
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
			document.title = "UNLOK Loyalty | Business";
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
			attr(div4, "id", "section-d42fa39a");
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
	child_ctx[9] = list[i];
	return child_ctx;
}

// (268:10) {#each hero_feature as feature }
function create_each_block$1(ctx) {
	let div;
	let h6;
	let t0_value = /*feature*/ ctx[9].title + "";
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
			attr(div, "class", "tag-yellow-small");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, h6);
			append_hydration(h6, t0);
			append_hydration(div, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*hero_feature*/ 16 && t0_value !== (t0_value = /*feature*/ ctx[9].title + "")) set_data(t0, t0_value);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function create_fragment$3(ctx) {
	let div7;
	let section;
	let div6;
	let div5;
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
	let div4;
	let img;
	let img_src_value;
	let img_alt_value;
	let each_value = /*hero_feature*/ ctx[4];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div7 = element("div");
			section = element("section");
			div6 = element("div");
			div5 = element("div");
			div0 = element("div");
			h10 = element("h1");
			t0 = text(/*hero_title1*/ ctx[0]);
			t1 = space();
			div1 = element("div");
			h11 = element("h1");
			t2 = text(/*hero_title2*/ ctx[1]);
			t3 = space();
			div3 = element("div");
			div2 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t4 = space();
			p = element("p");
			t5 = text(/*hero_description*/ ctx[2]);
			t6 = space();
			div4 = element("div");
			img = element("img");
			this.h();
		},
		l(nodes) {
			div7 = claim_element(nodes, "DIV", { class: true, id: true });
			var div7_nodes = children(div7);
			section = claim_element(div7_nodes, "SECTION", {});
			var section_nodes = children(section);
			div6 = claim_element(section_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div0 = claim_element(div5_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h10 = claim_element(div0_nodes, "H1", { class: true });
			var h10_nodes = children(h10);
			t0 = claim_text(h10_nodes, /*hero_title1*/ ctx[0]);
			h10_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div5_nodes);
			div1 = claim_element(div5_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h11 = claim_element(div1_nodes, "H1", { class: true });
			var h11_nodes = children(h11);
			t2 = claim_text(h11_nodes, /*hero_title2*/ ctx[1]);
			h11_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t3 = claim_space(div5_nodes);
			div3 = claim_element(div5_nodes, "DIV", { class: true });
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
			t5 = claim_text(p_nodes, /*hero_description*/ ctx[2]);
			p_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t6 = claim_space(div5_nodes);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			img = claim_element(div4_nodes, "IMG", { class: true, src: true, alt: true });
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h10, "class", "svelte-qgaks");
			attr(div0, "class", "hero-text-container1 svelte-qgaks");
			attr(h11, "class", "svelte-qgaks");
			attr(div1, "class", "hero-text-container2 svelte-qgaks");
			attr(div2, "class", "hero-feature-tag-container svelte-qgaks");
			attr(p, "class", "h650 svelte-qgaks");
			attr(div3, "class", "hero-feature-container svelte-qgaks");
			attr(img, "class", "hero-image-1 svelte-qgaks");
			if (!src_url_equal(img.src, img_src_value = /*hero_image_1*/ ctx[3].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*hero_image_1*/ ctx[3].alt);
			attr(div4, "class", "hero-feature-container svelte-qgaks");
			attr(div5, "class", "hero-container svelte-qgaks");
			attr(div6, "class", "hero-wrapper svelte-qgaks");
			attr(div7, "class", "section");
			attr(div7, "id", "section-ee1e4a1e");
		},
		m(target, anchor) {
			insert_hydration(target, div7, anchor);
			append_hydration(div7, section);
			append_hydration(section, div6);
			append_hydration(div6, div5);
			append_hydration(div5, div0);
			append_hydration(div0, h10);
			append_hydration(h10, t0);
			append_hydration(div5, t1);
			append_hydration(div5, div1);
			append_hydration(div1, h11);
			append_hydration(h11, t2);
			append_hydration(div5, t3);
			append_hydration(div5, div3);
			append_hydration(div3, div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div2, null);
				}
			}

			append_hydration(div3, t4);
			append_hydration(div3, p);
			append_hydration(p, t5);
			append_hydration(div5, t6);
			append_hydration(div5, div4);
			append_hydration(div4, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*hero_title1*/ 1) set_data(t0, /*hero_title1*/ ctx[0]);
			if (dirty & /*hero_title2*/ 2) set_data(t2, /*hero_title2*/ ctx[1]);

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

			if (dirty & /*hero_description*/ 4) set_data(t5, /*hero_description*/ ctx[2]);

			if (dirty & /*hero_image_1*/ 8 && !src_url_equal(img.src, img_src_value = /*hero_image_1*/ ctx[3].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*hero_image_1*/ 8 && img_alt_value !== (img_alt_value = /*hero_image_1*/ ctx[3].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div7);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { hero_title1 } = $$props;
	let { hero_title2 } = $$props;
	let { hero_description } = $$props;
	let { hero_image_1 } = $$props;
	let { hero_feature } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('hero_title1' in $$props) $$invalidate(0, hero_title1 = $$props.hero_title1);
		if ('hero_title2' in $$props) $$invalidate(1, hero_title2 = $$props.hero_title2);
		if ('hero_description' in $$props) $$invalidate(2, hero_description = $$props.hero_description);
		if ('hero_image_1' in $$props) $$invalidate(3, hero_image_1 = $$props.hero_image_1);
		if ('hero_feature' in $$props) $$invalidate(4, hero_feature = $$props.hero_feature);
	};

	return [
		hero_title1,
		hero_title2,
		hero_description,
		hero_image_1,
		hero_feature,
		favicon
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 5,
			hero_title1: 0,
			hero_title2: 1,
			hero_description: 2,
			hero_image_1: 3,
			hero_feature: 4
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$4(ctx) {
	let div5;
	let div4;
	let div3;
	let div0;
	let h3;
	let t0;
	let t1;
	let img;
	let img_src_value;
	let img_alt_value;
	let t2;
	let div2;
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
			div5 = element("div");
			div4 = element("div");
			div3 = element("div");
			div0 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title*/ ctx[0]);
			t1 = space();
			img = element("img");
			t2 = space();
			div2 = element("div");
			p = element("p");
			t3 = text(/*content_description*/ ctx[1]);
			t4 = space();
			div1 = element("div");
			a = element("a");
			t5 = text(t5_value);
			this.h();
		},
		l(nodes) {
			div5 = claim_element(nodes, "DIV", { class: true, id: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { id: true, class: true });
			var div0_nodes = children(div0);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			img = claim_element(div0_nodes, "IMG", { src: true, alt: true, class: true });
			div0_nodes.forEach(detach);
			t2 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { id: true, class: true });
			var div2_nodes = children(div2);
			p = claim_element(div2_nodes, "P", { class: true });
			var p_nodes = children(p);
			t3 = claim_text(p_nodes, /*content_description*/ ctx[1]);
			p_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a = claim_element(div1_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t5 = claim_text(a_nodes, t5_value);
			a_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-5x3l83");
			if (!src_url_equal(img.src, img_src_value = /*content_image*/ ctx[3].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*content_image*/ ctx[3].alt);
			attr(img, "class", "svelte-5x3l83");
			attr(div0, "id", "first");
			attr(div0, "class", "svelte-5x3l83");
			attr(p, "class", "p-large svelte-5x3l83");
			attr(a, "href", a_href_value = /*action_button*/ ctx[2].url);
			attr(a, "class", "primary-large-button svelte-5x3l83");
			attr(div1, "class", "button-wrapper svelte-5x3l83");
			attr(div2, "id", "second");
			attr(div2, "class", "svelte-5x3l83");
			attr(div3, "class", "wrapper svelte-5x3l83");
			attr(div4, "class", "container svelte-5x3l83");
			attr(div5, "class", "section");
			attr(div5, "id", "section-0bc9d5cb");
		},
		m(target, anchor) {
			insert_hydration(target, div5, anchor);
			append_hydration(div5, div4);
			append_hydration(div4, div3);
			append_hydration(div3, div0);
			append_hydration(div0, h3);
			append_hydration(h3, t0);
			append_hydration(div0, t1);
			append_hydration(div0, img);
			append_hydration(div3, t2);
			append_hydration(div3, div2);
			append_hydration(div2, p);
			append_hydration(p, t3);
			append_hydration(div2, t4);
			append_hydration(div2, div1);
			append_hydration(div1, a);
			append_hydration(a, t5);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title*/ 1) set_data(t0, /*content_title*/ ctx[0]);

			if (dirty & /*content_image*/ 8 && !src_url_equal(img.src, img_src_value = /*content_image*/ ctx[3].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*content_image*/ 8 && img_alt_value !== (img_alt_value = /*content_image*/ ctx[3].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*content_description*/ 2) set_data(t3, /*content_description*/ ctx[1]);
			if (dirty & /*action_button*/ 4 && t5_value !== (t5_value = /*action_button*/ ctx[2].label + "")) set_data(t5, t5_value);

			if (dirty & /*action_button*/ 4 && a_href_value !== (a_href_value = /*action_button*/ ctx[2].url)) {
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

function instance$4($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_description } = $$props;
	let { action_button } = $$props;
	let { content_image } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_description' in $$props) $$invalidate(1, content_description = $$props.content_description);
		if ('action_button' in $$props) $$invalidate(2, action_button = $$props.action_button);
		if ('content_image' in $$props) $$invalidate(3, content_image = $$props.content_image);
	};

	return [content_title, content_description, action_button, content_image, favicon];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			favicon: 4,
			content_title: 0,
			content_description: 1,
			action_button: 2,
			content_image: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$5(ctx) {
	let div13;
	let div12;
	let div11;
	let div10;
	let div0;
	let h3;
	let t0;
	let t1;
	let div1;
	let h4;
	let t2;
	let t3;
	let div9;
	let div8;
	let div4;
	let div2;
	let h60;
	let t4_value = /*content_1*/ ctx[2].title + "";
	let t4;
	let t5;
	let p0;
	let t6_value = /*content_1*/ ctx[2].description + "";
	let t6;
	let t7;
	let h61;
	let t8_value = /*content_2*/ ctx[3].title + "";
	let t8;
	let t9;
	let p1;
	let t10_value = /*content_2*/ ctx[3].description + "";
	let t10;
	let t11;
	let h62;
	let t12_value = /*content_5*/ ctx[6].title + "";
	let t12;
	let t13;
	let p2;
	let t14_value = /*content_5*/ ctx[6].description + "";
	let t14;
	let t15;
	let img0;
	let img0_src_value;
	let img0_alt_value;
	let t16;
	let img1;
	let img1_src_value;
	let img1_alt_value;
	let t17;
	let div3;
	let h63;
	let t18_value = /*content_3*/ ctx[4].title + "";
	let t18;
	let t19;
	let p3;
	let t20_value = /*content_3*/ ctx[4].description + "";
	let t20;
	let t21;
	let h64;
	let t22_value = /*content_4*/ ctx[5].title + "";
	let t22;
	let t23;
	let p4;
	let t24_value = /*content_4*/ ctx[5].description + "";
	let t24;
	let t25;
	let h65;
	let t26_value = /*content_6*/ ctx[7].title + "";
	let t26;
	let t27;
	let p5;
	let t28_value = /*content_6*/ ctx[7].description + "";
	let t28;
	let t29;
	let div7;
	let div5;
	let t30;
	let div6;
	let h66;
	let t31_value = /*content_1*/ ctx[2].title + "";
	let t31;
	let t32;
	let p6;
	let t33_value = /*content_1*/ ctx[2].description + "";
	let t33;
	let t34;
	let h67;
	let t35_value = /*content_2*/ ctx[3].title + "";
	let t35;
	let t36;
	let p7;
	let t37_value = /*content_2*/ ctx[3].description + "";
	let t37;
	let t38;
	let h68;
	let t39_value = /*content_3*/ ctx[4].title + "";
	let t39;
	let t40;
	let p8;
	let t41_value = /*content_3*/ ctx[4].description + "";
	let t41;
	let t42;
	let h69;
	let t43_value = /*content_4*/ ctx[5].title + "";
	let t43;
	let t44;
	let p9;
	let t45_value = /*content_4*/ ctx[5].description + "";
	let t45;
	let t46;
	let h610;
	let t47_value = /*content_5*/ ctx[6].title + "";
	let t47;
	let t48;
	let p10;
	let t49_value = /*content_5*/ ctx[6].description + "";
	let t49;
	let t50;
	let h611;
	let t51_value = /*content_6*/ ctx[7].title + "";
	let t51;
	let t52;
	let p11;
	let t53_value = /*content_6*/ ctx[7].description + "";
	let t53;

	return {
		c() {
			div13 = element("div");
			div12 = element("div");
			div11 = element("div");
			div10 = element("div");
			div0 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title_1*/ ctx[0]);
			t1 = space();
			div1 = element("div");
			h4 = element("h4");
			t2 = text(/*content_title_2*/ ctx[1]);
			t3 = space();
			div9 = element("div");
			div8 = element("div");
			div4 = element("div");
			div2 = element("div");
			h60 = element("h6");
			t4 = text(t4_value);
			t5 = space();
			p0 = element("p");
			t6 = text(t6_value);
			t7 = space();
			h61 = element("h6");
			t8 = text(t8_value);
			t9 = space();
			p1 = element("p");
			t10 = text(t10_value);
			t11 = space();
			h62 = element("h6");
			t12 = text(t12_value);
			t13 = space();
			p2 = element("p");
			t14 = text(t14_value);
			t15 = space();
			img0 = element("img");
			t16 = space();
			img1 = element("img");
			t17 = space();
			div3 = element("div");
			h63 = element("h6");
			t18 = text(t18_value);
			t19 = space();
			p3 = element("p");
			t20 = text(t20_value);
			t21 = space();
			h64 = element("h6");
			t22 = text(t22_value);
			t23 = space();
			p4 = element("p");
			t24 = text(t24_value);
			t25 = space();
			h65 = element("h6");
			t26 = text(t26_value);
			t27 = space();
			p5 = element("p");
			t28 = text(t28_value);
			t29 = space();
			div7 = element("div");
			div5 = element("div");
			t30 = space();
			div6 = element("div");
			h66 = element("h6");
			t31 = text(t31_value);
			t32 = space();
			p6 = element("p");
			t33 = text(t33_value);
			t34 = space();
			h67 = element("h6");
			t35 = text(t35_value);
			t36 = space();
			p7 = element("p");
			t37 = text(t37_value);
			t38 = space();
			h68 = element("h6");
			t39 = text(t39_value);
			t40 = space();
			p8 = element("p");
			t41 = text(t41_value);
			t42 = space();
			h69 = element("h6");
			t43 = text(t43_value);
			t44 = space();
			p9 = element("p");
			t45 = text(t45_value);
			t46 = space();
			h610 = element("h6");
			t47 = text(t47_value);
			t48 = space();
			p10 = element("p");
			t49 = text(t49_value);
			t50 = space();
			h611 = element("h6");
			t51 = text(t51_value);
			t52 = space();
			p11 = element("p");
			t53 = text(t53_value);
			this.h();
		},
		l(nodes) {
			div13 = claim_element(nodes, "DIV", { class: true, id: true });
			var div13_nodes = children(div13);
			div12 = claim_element(div13_nodes, "DIV", { class: true });
			var div12_nodes = children(div12);
			div11 = claim_element(div12_nodes, "DIV", { class: true });
			var div11_nodes = children(div11);
			div10 = claim_element(div11_nodes, "DIV", { class: true });
			var div10_nodes = children(div10);
			div0 = claim_element(div10_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title_1*/ ctx[0]);
			h3_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div10_nodes);
			div1 = claim_element(div10_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h4 = claim_element(div1_nodes, "H4", { class: true });
			var h4_nodes = children(h4);
			t2 = claim_text(h4_nodes, /*content_title_2*/ ctx[1]);
			h4_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t3 = claim_space(div10_nodes);
			div9 = claim_element(div10_nodes, "DIV", { class: true });
			var div9_nodes = children(div9);
			div8 = claim_element(div9_nodes, "DIV", {});
			var div8_nodes = children(div8);
			div4 = claim_element(div8_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div2 = claim_element(div4_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h60 = claim_element(div2_nodes, "H6", { class: true });
			var h60_nodes = children(h60);
			t4 = claim_text(h60_nodes, t4_value);
			h60_nodes.forEach(detach);
			t5 = claim_space(div2_nodes);
			p0 = claim_element(div2_nodes, "P", { class: true });
			var p0_nodes = children(p0);
			t6 = claim_text(p0_nodes, t6_value);
			p0_nodes.forEach(detach);
			t7 = claim_space(div2_nodes);
			h61 = claim_element(div2_nodes, "H6", { class: true });
			var h61_nodes = children(h61);
			t8 = claim_text(h61_nodes, t8_value);
			h61_nodes.forEach(detach);
			t9 = claim_space(div2_nodes);
			p1 = claim_element(div2_nodes, "P", { class: true });
			var p1_nodes = children(p1);
			t10 = claim_text(p1_nodes, t10_value);
			p1_nodes.forEach(detach);
			t11 = claim_space(div2_nodes);
			h62 = claim_element(div2_nodes, "H6", { class: true });
			var h62_nodes = children(h62);
			t12 = claim_text(h62_nodes, t12_value);
			h62_nodes.forEach(detach);
			t13 = claim_space(div2_nodes);
			p2 = claim_element(div2_nodes, "P", { class: true });
			var p2_nodes = children(p2);
			t14 = claim_text(p2_nodes, t14_value);
			p2_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t15 = claim_space(div4_nodes);

			img0 = claim_element(div4_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			t16 = claim_space(div4_nodes);

			img1 = claim_element(div4_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			t17 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			h63 = claim_element(div3_nodes, "H6", { class: true });
			var h63_nodes = children(h63);
			t18 = claim_text(h63_nodes, t18_value);
			h63_nodes.forEach(detach);
			t19 = claim_space(div3_nodes);
			p3 = claim_element(div3_nodes, "P", { class: true });
			var p3_nodes = children(p3);
			t20 = claim_text(p3_nodes, t20_value);
			p3_nodes.forEach(detach);
			t21 = claim_space(div3_nodes);
			h64 = claim_element(div3_nodes, "H6", { class: true });
			var h64_nodes = children(h64);
			t22 = claim_text(h64_nodes, t22_value);
			h64_nodes.forEach(detach);
			t23 = claim_space(div3_nodes);
			p4 = claim_element(div3_nodes, "P", { class: true });
			var p4_nodes = children(p4);
			t24 = claim_text(p4_nodes, t24_value);
			p4_nodes.forEach(detach);
			t25 = claim_space(div3_nodes);
			h65 = claim_element(div3_nodes, "H6", { class: true });
			var h65_nodes = children(h65);
			t26 = claim_text(h65_nodes, t26_value);
			h65_nodes.forEach(detach);
			t27 = claim_space(div3_nodes);
			p5 = claim_element(div3_nodes, "P", { class: true });
			var p5_nodes = children(p5);
			t28 = claim_text(p5_nodes, t28_value);
			p5_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			t29 = claim_space(div8_nodes);
			div7 = claim_element(div8_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			div5 = claim_element(div7_nodes, "DIV", { class: true });
			children(div5).forEach(detach);
			t30 = claim_space(div7_nodes);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			h66 = claim_element(div6_nodes, "H6", { class: true });
			var h66_nodes = children(h66);
			t31 = claim_text(h66_nodes, t31_value);
			h66_nodes.forEach(detach);
			t32 = claim_space(div6_nodes);
			p6 = claim_element(div6_nodes, "P", { class: true });
			var p6_nodes = children(p6);
			t33 = claim_text(p6_nodes, t33_value);
			p6_nodes.forEach(detach);
			t34 = claim_space(div6_nodes);
			h67 = claim_element(div6_nodes, "H6", { class: true });
			var h67_nodes = children(h67);
			t35 = claim_text(h67_nodes, t35_value);
			h67_nodes.forEach(detach);
			t36 = claim_space(div6_nodes);
			p7 = claim_element(div6_nodes, "P", { class: true });
			var p7_nodes = children(p7);
			t37 = claim_text(p7_nodes, t37_value);
			p7_nodes.forEach(detach);
			t38 = claim_space(div6_nodes);
			h68 = claim_element(div6_nodes, "H6", { class: true });
			var h68_nodes = children(h68);
			t39 = claim_text(h68_nodes, t39_value);
			h68_nodes.forEach(detach);
			t40 = claim_space(div6_nodes);
			p8 = claim_element(div6_nodes, "P", { class: true });
			var p8_nodes = children(p8);
			t41 = claim_text(p8_nodes, t41_value);
			p8_nodes.forEach(detach);
			t42 = claim_space(div6_nodes);
			h69 = claim_element(div6_nodes, "H6", { class: true });
			var h69_nodes = children(h69);
			t43 = claim_text(h69_nodes, t43_value);
			h69_nodes.forEach(detach);
			t44 = claim_space(div6_nodes);
			p9 = claim_element(div6_nodes, "P", { class: true });
			var p9_nodes = children(p9);
			t45 = claim_text(p9_nodes, t45_value);
			p9_nodes.forEach(detach);
			t46 = claim_space(div6_nodes);
			h610 = claim_element(div6_nodes, "H6", { class: true });
			var h610_nodes = children(h610);
			t47 = claim_text(h610_nodes, t47_value);
			h610_nodes.forEach(detach);
			t48 = claim_space(div6_nodes);
			p10 = claim_element(div6_nodes, "P", { class: true });
			var p10_nodes = children(p10);
			t49 = claim_text(p10_nodes, t49_value);
			p10_nodes.forEach(detach);
			t50 = claim_space(div6_nodes);
			h611 = claim_element(div6_nodes, "H6", { class: true });
			var h611_nodes = children(h611);
			t51 = claim_text(h611_nodes, t51_value);
			h611_nodes.forEach(detach);
			t52 = claim_space(div6_nodes);
			p11 = claim_element(div6_nodes, "P", { class: true });
			var p11_nodes = children(p11);
			t53 = claim_text(p11_nodes, t53_value);
			p11_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			div9_nodes.forEach(detach);
			div10_nodes.forEach(detach);
			div11_nodes.forEach(detach);
			div12_nodes.forEach(detach);
			div13_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-tqcpt3");
			attr(div0, "class", "hero-text-container1 svelte-tqcpt3");
			attr(h4, "class", "svelte-tqcpt3");
			attr(div1, "class", "hero-text-container2 svelte-tqcpt3");
			attr(h60, "class", "h600 svelte-tqcpt3");
			attr(p0, "class", "p-medium svelte-tqcpt3");
			attr(h61, "class", "h600 svelte-tqcpt3");
			attr(p1, "class", "p-medium svelte-tqcpt3");
			attr(h62, "class", "h600 svelte-tqcpt3");
			attr(p2, "class", "p-medium svelte-tqcpt3");
			attr(div2, "class", "content-group-1-desktop");
			attr(img0, "id", "tree-desktop");
			if (!src_url_equal(img0.src, img0_src_value = /*content_image_desktop*/ ctx[8].url)) attr(img0, "src", img0_src_value);
			attr(img0, "alt", img0_alt_value = /*content_image_desktop*/ ctx[8].alt);
			attr(img0, "class", "svelte-tqcpt3");
			attr(img1, "id", "tree-small-desktop");
			if (!src_url_equal(img1.src, img1_src_value = /*content_image_small_desktop*/ ctx[9].url)) attr(img1, "src", img1_src_value);
			attr(img1, "alt", img1_alt_value = /*content_image_small_desktop*/ ctx[9].alt);
			attr(img1, "class", "svelte-tqcpt3");
			attr(h63, "class", "h600 svelte-tqcpt3");
			attr(p3, "class", "p-medium svelte-tqcpt3");
			attr(h64, "class", "h600 svelte-tqcpt3");
			attr(p4, "class", "p-medium svelte-tqcpt3");
			attr(h65, "class", "h600 svelte-tqcpt3");
			attr(p5, "class", "p-medium svelte-tqcpt3");
			attr(div3, "class", "content-group-2-desktop svelte-tqcpt3");
			attr(div4, "class", "content-group-desktop svelte-tqcpt3");
			attr(div5, "class", "bar svelte-tqcpt3");
			attr(h66, "class", "h600 svelte-tqcpt3");
			attr(p6, "class", "p-medium svelte-tqcpt3");
			attr(h67, "class", "h600 svelte-tqcpt3");
			attr(p7, "class", "p-medium svelte-tqcpt3");
			attr(h68, "class", "h600 svelte-tqcpt3");
			attr(p8, "class", "p-medium svelte-tqcpt3");
			attr(h69, "class", "h600 svelte-tqcpt3");
			attr(p9, "class", "p-medium svelte-tqcpt3");
			attr(h610, "class", "h600 svelte-tqcpt3");
			attr(p10, "class", "p-medium svelte-tqcpt3");
			attr(h611, "class", "h600 svelte-tqcpt3");
			attr(p11, "class", "p-medium svelte-tqcpt3");
			attr(div6, "class", "content-group-mobile svelte-tqcpt3");
			attr(div7, "class", "content-group-mobile-wrapper svelte-tqcpt3");
			attr(div9, "class", "content-group svelte-tqcpt3");
			attr(div10, "class", "section-container content svelte-tqcpt3");
			attr(div11, "class", "wrapper svelte-tqcpt3");
			attr(div12, "class", "container svelte-tqcpt3");
			attr(div13, "class", "section");
			attr(div13, "id", "section-30ae418e");
		},
		m(target, anchor) {
			insert_hydration(target, div13, anchor);
			append_hydration(div13, div12);
			append_hydration(div12, div11);
			append_hydration(div11, div10);
			append_hydration(div10, div0);
			append_hydration(div0, h3);
			append_hydration(h3, t0);
			append_hydration(div10, t1);
			append_hydration(div10, div1);
			append_hydration(div1, h4);
			append_hydration(h4, t2);
			append_hydration(div10, t3);
			append_hydration(div10, div9);
			append_hydration(div9, div8);
			append_hydration(div8, div4);
			append_hydration(div4, div2);
			append_hydration(div2, h60);
			append_hydration(h60, t4);
			append_hydration(div2, t5);
			append_hydration(div2, p0);
			append_hydration(p0, t6);
			append_hydration(div2, t7);
			append_hydration(div2, h61);
			append_hydration(h61, t8);
			append_hydration(div2, t9);
			append_hydration(div2, p1);
			append_hydration(p1, t10);
			append_hydration(div2, t11);
			append_hydration(div2, h62);
			append_hydration(h62, t12);
			append_hydration(div2, t13);
			append_hydration(div2, p2);
			append_hydration(p2, t14);
			append_hydration(div4, t15);
			append_hydration(div4, img0);
			append_hydration(div4, t16);
			append_hydration(div4, img1);
			append_hydration(div4, t17);
			append_hydration(div4, div3);
			append_hydration(div3, h63);
			append_hydration(h63, t18);
			append_hydration(div3, t19);
			append_hydration(div3, p3);
			append_hydration(p3, t20);
			append_hydration(div3, t21);
			append_hydration(div3, h64);
			append_hydration(h64, t22);
			append_hydration(div3, t23);
			append_hydration(div3, p4);
			append_hydration(p4, t24);
			append_hydration(div3, t25);
			append_hydration(div3, h65);
			append_hydration(h65, t26);
			append_hydration(div3, t27);
			append_hydration(div3, p5);
			append_hydration(p5, t28);
			append_hydration(div8, t29);
			append_hydration(div8, div7);
			append_hydration(div7, div5);
			append_hydration(div7, t30);
			append_hydration(div7, div6);
			append_hydration(div6, h66);
			append_hydration(h66, t31);
			append_hydration(div6, t32);
			append_hydration(div6, p6);
			append_hydration(p6, t33);
			append_hydration(div6, t34);
			append_hydration(div6, h67);
			append_hydration(h67, t35);
			append_hydration(div6, t36);
			append_hydration(div6, p7);
			append_hydration(p7, t37);
			append_hydration(div6, t38);
			append_hydration(div6, h68);
			append_hydration(h68, t39);
			append_hydration(div6, t40);
			append_hydration(div6, p8);
			append_hydration(p8, t41);
			append_hydration(div6, t42);
			append_hydration(div6, h69);
			append_hydration(h69, t43);
			append_hydration(div6, t44);
			append_hydration(div6, p9);
			append_hydration(p9, t45);
			append_hydration(div6, t46);
			append_hydration(div6, h610);
			append_hydration(h610, t47);
			append_hydration(div6, t48);
			append_hydration(div6, p10);
			append_hydration(p10, t49);
			append_hydration(div6, t50);
			append_hydration(div6, h611);
			append_hydration(h611, t51);
			append_hydration(div6, t52);
			append_hydration(div6, p11);
			append_hydration(p11, t53);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title_1*/ 1) set_data(t0, /*content_title_1*/ ctx[0]);
			if (dirty & /*content_title_2*/ 2) set_data(t2, /*content_title_2*/ ctx[1]);
			if (dirty & /*content_1*/ 4 && t4_value !== (t4_value = /*content_1*/ ctx[2].title + "")) set_data(t4, t4_value);
			if (dirty & /*content_1*/ 4 && t6_value !== (t6_value = /*content_1*/ ctx[2].description + "")) set_data(t6, t6_value);
			if (dirty & /*content_2*/ 8 && t8_value !== (t8_value = /*content_2*/ ctx[3].title + "")) set_data(t8, t8_value);
			if (dirty & /*content_2*/ 8 && t10_value !== (t10_value = /*content_2*/ ctx[3].description + "")) set_data(t10, t10_value);
			if (dirty & /*content_5*/ 64 && t12_value !== (t12_value = /*content_5*/ ctx[6].title + "")) set_data(t12, t12_value);
			if (dirty & /*content_5*/ 64 && t14_value !== (t14_value = /*content_5*/ ctx[6].description + "")) set_data(t14, t14_value);

			if (dirty & /*content_image_desktop*/ 256 && !src_url_equal(img0.src, img0_src_value = /*content_image_desktop*/ ctx[8].url)) {
				attr(img0, "src", img0_src_value);
			}

			if (dirty & /*content_image_desktop*/ 256 && img0_alt_value !== (img0_alt_value = /*content_image_desktop*/ ctx[8].alt)) {
				attr(img0, "alt", img0_alt_value);
			}

			if (dirty & /*content_image_small_desktop*/ 512 && !src_url_equal(img1.src, img1_src_value = /*content_image_small_desktop*/ ctx[9].url)) {
				attr(img1, "src", img1_src_value);
			}

			if (dirty & /*content_image_small_desktop*/ 512 && img1_alt_value !== (img1_alt_value = /*content_image_small_desktop*/ ctx[9].alt)) {
				attr(img1, "alt", img1_alt_value);
			}

			if (dirty & /*content_3*/ 16 && t18_value !== (t18_value = /*content_3*/ ctx[4].title + "")) set_data(t18, t18_value);
			if (dirty & /*content_3*/ 16 && t20_value !== (t20_value = /*content_3*/ ctx[4].description + "")) set_data(t20, t20_value);
			if (dirty & /*content_4*/ 32 && t22_value !== (t22_value = /*content_4*/ ctx[5].title + "")) set_data(t22, t22_value);
			if (dirty & /*content_4*/ 32 && t24_value !== (t24_value = /*content_4*/ ctx[5].description + "")) set_data(t24, t24_value);
			if (dirty & /*content_6*/ 128 && t26_value !== (t26_value = /*content_6*/ ctx[7].title + "")) set_data(t26, t26_value);
			if (dirty & /*content_6*/ 128 && t28_value !== (t28_value = /*content_6*/ ctx[7].description + "")) set_data(t28, t28_value);
			if (dirty & /*content_1*/ 4 && t31_value !== (t31_value = /*content_1*/ ctx[2].title + "")) set_data(t31, t31_value);
			if (dirty & /*content_1*/ 4 && t33_value !== (t33_value = /*content_1*/ ctx[2].description + "")) set_data(t33, t33_value);
			if (dirty & /*content_2*/ 8 && t35_value !== (t35_value = /*content_2*/ ctx[3].title + "")) set_data(t35, t35_value);
			if (dirty & /*content_2*/ 8 && t37_value !== (t37_value = /*content_2*/ ctx[3].description + "")) set_data(t37, t37_value);
			if (dirty & /*content_3*/ 16 && t39_value !== (t39_value = /*content_3*/ ctx[4].title + "")) set_data(t39, t39_value);
			if (dirty & /*content_3*/ 16 && t41_value !== (t41_value = /*content_3*/ ctx[4].description + "")) set_data(t41, t41_value);
			if (dirty & /*content_4*/ 32 && t43_value !== (t43_value = /*content_4*/ ctx[5].title + "")) set_data(t43, t43_value);
			if (dirty & /*content_4*/ 32 && t45_value !== (t45_value = /*content_4*/ ctx[5].description + "")) set_data(t45, t45_value);
			if (dirty & /*content_5*/ 64 && t47_value !== (t47_value = /*content_5*/ ctx[6].title + "")) set_data(t47, t47_value);
			if (dirty & /*content_5*/ 64 && t49_value !== (t49_value = /*content_5*/ ctx[6].description + "")) set_data(t49, t49_value);
			if (dirty & /*content_6*/ 128 && t51_value !== (t51_value = /*content_6*/ ctx[7].title + "")) set_data(t51, t51_value);
			if (dirty & /*content_6*/ 128 && t53_value !== (t53_value = /*content_6*/ ctx[7].description + "")) set_data(t53, t53_value);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div13);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title_1 } = $$props;
	let { content_title_2 } = $$props;
	let { content_1 } = $$props;
	let { content_2 } = $$props;
	let { content_3 } = $$props;
	let { content_4 } = $$props;
	let { content_5 } = $$props;
	let { content_6 } = $$props;
	let { content_image_desktop } = $$props;
	let { content_image_small_desktop } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(10, favicon = $$props.favicon);
		if ('content_title_1' in $$props) $$invalidate(0, content_title_1 = $$props.content_title_1);
		if ('content_title_2' in $$props) $$invalidate(1, content_title_2 = $$props.content_title_2);
		if ('content_1' in $$props) $$invalidate(2, content_1 = $$props.content_1);
		if ('content_2' in $$props) $$invalidate(3, content_2 = $$props.content_2);
		if ('content_3' in $$props) $$invalidate(4, content_3 = $$props.content_3);
		if ('content_4' in $$props) $$invalidate(5, content_4 = $$props.content_4);
		if ('content_5' in $$props) $$invalidate(6, content_5 = $$props.content_5);
		if ('content_6' in $$props) $$invalidate(7, content_6 = $$props.content_6);
		if ('content_image_desktop' in $$props) $$invalidate(8, content_image_desktop = $$props.content_image_desktop);
		if ('content_image_small_desktop' in $$props) $$invalidate(9, content_image_small_desktop = $$props.content_image_small_desktop);
	};

	return [
		content_title_1,
		content_title_2,
		content_1,
		content_2,
		content_3,
		content_4,
		content_5,
		content_6,
		content_image_desktop,
		content_image_small_desktop,
		favicon
	];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			favicon: 10,
			content_title_1: 0,
			content_title_2: 1,
			content_1: 2,
			content_2: 3,
			content_3: 4,
			content_4: 5,
			content_5: 6,
			content_6: 7,
			content_image_desktop: 8,
			content_image_small_desktop: 9
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

// (330:8) {#if content_tag}
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
			attr(div, "class", "tag-pink-large svelte-1v6x5sr");
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

// (341:10) {#each content_card as card}
function create_each_block_2(ctx) {
	let div3;
	let div1;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let div0;
	let h60;
	let t1_value = /*card*/ ctx[17].title + "";
	let t1;
	let t2;
	let h61;
	let t3_value = /*card*/ ctx[17].subtitle + "";
	let t3;
	let t4;
	let div2;
	let p;
	let t5_value = /*card*/ ctx[17].description + "";
	let t5;
	let t6;

	return {
		c() {
			div3 = element("div");
			div1 = element("div");
			img = element("img");
			t0 = space();
			div0 = element("div");
			h60 = element("h6");
			t1 = text(t1_value);
			t2 = space();
			h61 = element("h6");
			t3 = text(t3_value);
			t4 = space();
			div2 = element("div");
			p = element("p");
			t5 = text(t5_value);
			t6 = space();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			img = claim_element(div1_nodes, "IMG", { src: true, alt: true, class: true });
			t0 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", {});
			var div0_nodes = children(div0);
			h60 = claim_element(div0_nodes, "H6", {});
			var h60_nodes = children(h60);
			t1 = claim_text(h60_nodes, t1_value);
			h60_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			h61 = claim_element(div0_nodes, "H6", { class: true });
			var h61_nodes = children(h61);
			t3 = claim_text(h61_nodes, t3_value);
			h61_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t4 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			p = claim_element(div2_nodes, "P", { class: true });
			var p_nodes = children(p);
			t5 = claim_text(p_nodes, t5_value);
			p_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t6 = claim_space(div3_nodes);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*card*/ ctx[17].image.alt);
			attr(img, "class", "svelte-1v6x5sr");
			attr(h61, "class", "h800");
			attr(div1, "class", "card-title-wrapper svelte-1v6x5sr");
			attr(p, "class", "p-medium");
			attr(div2, "class", "card-content-wrapper svelte-1v6x5sr");
			attr(div3, "class", "card-wrapper slider svelte-1v6x5sr");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div1);
			append_hydration(div1, img);
			append_hydration(div1, t0);
			append_hydration(div1, div0);
			append_hydration(div0, h60);
			append_hydration(h60, t1);
			append_hydration(div0, t2);
			append_hydration(div0, h61);
			append_hydration(h61, t3);
			append_hydration(div3, t4);
			append_hydration(div3, div2);
			append_hydration(div2, p);
			append_hydration(p, t5);
			append_hydration(div3, t6);
		},
		p(ctx, dirty) {
			if (dirty & /*content_card*/ 8 && !src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*content_card*/ 8 && img_alt_value !== (img_alt_value = /*card*/ ctx[17].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*content_card*/ 8 && t1_value !== (t1_value = /*card*/ ctx[17].title + "")) set_data(t1, t1_value);
			if (dirty & /*content_card*/ 8 && t3_value !== (t3_value = /*card*/ ctx[17].subtitle + "")) set_data(t3, t3_value);
			if (dirty & /*content_card*/ 8 && t5_value !== (t5_value = /*card*/ ctx[17].description + "")) set_data(t5, t5_value);
		},
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

// (359:8) {#each content_card as card}
function create_each_block_1$1(ctx) {
	let div3;
	let div1;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let div0;
	let h60;
	let t1_value = /*card*/ ctx[17].title + "";
	let t1;
	let t2;
	let h61;
	let t3_value = /*card*/ ctx[17].subtitle + "";
	let t3;
	let t4;
	let div2;
	let p;
	let t5_value = /*card*/ ctx[17].description + "";
	let t5;
	let t6;

	return {
		c() {
			div3 = element("div");
			div1 = element("div");
			img = element("img");
			t0 = space();
			div0 = element("div");
			h60 = element("h6");
			t1 = text(t1_value);
			t2 = space();
			h61 = element("h6");
			t3 = text(t3_value);
			t4 = space();
			div2 = element("div");
			p = element("p");
			t5 = text(t5_value);
			t6 = space();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			img = claim_element(div1_nodes, "IMG", { src: true, alt: true, class: true });
			t0 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", {});
			var div0_nodes = children(div0);
			h60 = claim_element(div0_nodes, "H6", {});
			var h60_nodes = children(h60);
			t1 = claim_text(h60_nodes, t1_value);
			h60_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			h61 = claim_element(div0_nodes, "H6", { class: true });
			var h61_nodes = children(h61);
			t3 = claim_text(h61_nodes, t3_value);
			h61_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t4 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			p = claim_element(div2_nodes, "P", { class: true });
			var p_nodes = children(p);
			t5 = claim_text(p_nodes, t5_value);
			p_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t6 = claim_space(div3_nodes);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*card*/ ctx[17].image.alt);
			attr(img, "class", "svelte-1v6x5sr");
			attr(h61, "class", "h800");
			attr(div1, "class", "card-title-wrapper svelte-1v6x5sr");
			attr(p, "class", "p-medium");
			attr(div2, "class", "card-content-wrapper svelte-1v6x5sr");
			attr(div3, "class", "card-wrapper slider svelte-1v6x5sr");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div1);
			append_hydration(div1, img);
			append_hydration(div1, t0);
			append_hydration(div1, div0);
			append_hydration(div0, h60);
			append_hydration(h60, t1);
			append_hydration(div0, t2);
			append_hydration(div0, h61);
			append_hydration(h61, t3);
			append_hydration(div3, t4);
			append_hydration(div3, div2);
			append_hydration(div2, p);
			append_hydration(p, t5);
			append_hydration(div3, t6);
		},
		p(ctx, dirty) {
			if (dirty & /*content_card*/ 8 && !src_url_equal(img.src, img_src_value = /*card*/ ctx[17].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*content_card*/ 8 && img_alt_value !== (img_alt_value = /*card*/ ctx[17].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*content_card*/ 8 && t1_value !== (t1_value = /*card*/ ctx[17].title + "")) set_data(t1, t1_value);
			if (dirty & /*content_card*/ 8 && t3_value !== (t3_value = /*card*/ ctx[17].subtitle + "")) set_data(t3, t3_value);
			if (dirty & /*content_card*/ 8 && t5_value !== (t5_value = /*card*/ ctx[17].description + "")) set_data(t5, t5_value);
		},
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

// (379:6) {#each data as d, i}
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
				id: true,
				name: true,
				class: true
			});

			this.h();
		},
		h() {
			attr(input, "type", "radio");
			attr(input, "id", input_id_value = /*i*/ ctx[16]);
			attr(input, "name", "slider-radio");
			input.value = input_value_value = /*i*/ ctx[16];
			input.checked = input_checked_value = /*select*/ ctx[6] == /*i*/ ctx[16];
			attr(input, "class", "svelte-1v6x5sr");
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

function create_fragment$6(ctx) {
	let div9;
	let div8;
	let div7;
	let div3;
	let div1;
	let t0;
	let div0;
	let h4;
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
			h4 = element("h4");
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
			h4 = claim_element(div0_nodes, "H4", {});
			var h4_nodes = children(h4);
			t1 = claim_text(h4_nodes, /*content_title*/ ctx[1]);
			h4_nodes.forEach(detach);
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
			attr(div0, "class", "section-container content svelte-1v6x5sr");
			attr(div1, "class", "content-header-wrapper svelte-1v6x5sr");
			attr(div2, "class", "card-container-desktop svelte-1v6x5sr");
			attr(div3, "class", "content-wrapper svelte-1v6x5sr");
			attr(div4, "class", "siema svelte-1v6x5sr");
			attr(div5, "class", "card-container-mobile svelte-1v6x5sr");
			attr(div6, "class", "bullet svelte-1v6x5sr");
			attr(div7, "class", "wrapper svelte-1v6x5sr");
			attr(div8, "class", "container svelte-1v6x5sr");
			attr(div9, "class", "section");
			attr(div9, "id", "section-bd43a38d");
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
			append_hydration(div0, h4);
			append_hydration(h4, t1);
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

function instance$6($$self, $$props, $$invalidate) {
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
				selector: ".siema",
				duration: 200,
				easing: "ease-in-out",
				perPage: {
					0: 1, // 2 items for viewport wider than 800px
					540: 2,
					865: 3, // 3 items for viewport wider than 1240px
					1020: 4
				}, // 0: 1, // 2 items for viewport wider than 800px
				// 768: 2,
				// 1024: 3
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

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
			favicon: 8,
			content_tag: 0,
			content_title: 1,
			content_paragraph_1: 2,
			content_card: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$7(ctx) {
	let div2;
	let div1;
	let div0;
	let h3;
	let t0;
	let t1;
	let p;
	let t2;
	let t3;
	let a;
	let t4_value = /*action_button*/ ctx[2].label + "";
	let t4;
	let a_href_value;

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			h3 = element("h3");
			t0 = text(/*content_title*/ ctx[0]);
			t1 = space();
			p = element("p");
			t2 = text(/*content_description*/ ctx[1]);
			t3 = space();
			a = element("a");
			t4 = text(t4_value);
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*content_title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			p = claim_element(div0_nodes, "P", { class: true });
			var p_nodes = children(p);
			t2 = claim_text(p_nodes, /*content_description*/ ctx[1]);
			p_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			a = claim_element(div0_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t4 = claim_text(a_nodes, t4_value);
			a_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-19jc1fy");
			attr(p, "class", "p-large svelte-19jc1fy");
			attr(a, "href", a_href_value = /*action_button*/ ctx[2].url);
			attr(a, "class", "primary-large-button svelte-19jc1fy");
			attr(div0, "class", "wrapper svelte-19jc1fy");
			attr(div1, "class", "container svelte-19jc1fy");
			attr(div2, "class", "section");
			attr(div2, "id", "section-620a3d3c");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			append_hydration(div0, h3);
			append_hydration(h3, t0);
			append_hydration(div0, t1);
			append_hydration(div0, p);
			append_hydration(p, t2);
			append_hydration(div0, t3);
			append_hydration(div0, a);
			append_hydration(a, t4);
		},
		p(ctx, [dirty]) {
			if (dirty & /*content_title*/ 1) set_data(t0, /*content_title*/ ctx[0]);
			if (dirty & /*content_description*/ 2) set_data(t2, /*content_description*/ ctx[1]);
			if (dirty & /*action_button*/ 4 && t4_value !== (t4_value = /*action_button*/ ctx[2].label + "")) set_data(t4, t4_value);

			if (dirty & /*action_button*/ 4 && a_href_value !== (a_href_value = /*action_button*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { content_title } = $$props;
	let { content_description } = $$props;
	let { action_button } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('content_title' in $$props) $$invalidate(0, content_title = $$props.content_title);
		if ('content_description' in $$props) $$invalidate(1, content_description = $$props.content_description);
		if ('action_button' in $$props) $$invalidate(2, action_button = $$props.action_button);
	};

	return [content_title, content_description, action_button, favicon];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			favicon: 3,
			content_title: 0,
			content_description: 1,
			action_button: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	return child_ctx;
}

// (70:4) {#each nav as { link }}
function create_each_block$3(ctx) {
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

function create_fragment$8(ctx) {
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
		each_blocks[i] = create_each_block$3(get_each_context$3(ctx, each_value, i));
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
			attr(div, "id", "section-31ea9835");
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
					const child_ctx = get_each_context$3(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$3(child_ctx);
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

function instance$8($$self, $$props, $$invalidate) {
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

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$8, create_fragment$8, safe_not_equal, { favicon: 2, nav: 0, copyright: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function instance$9($$self, $$props, $$invalidate) {
	let { favicon } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
	};

	return [favicon];
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$9, null, safe_not_equal, { favicon: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$9(ctx) {
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
				hero_title1: "Welcome to",
				hero_title2: "UNLOK",
				hero_description: "Unleash the Power of Blockchain Rewards",
				hero_image_1: {
					"alt": "Blockchain Business",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686084649000business-banner.png",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686084649000business-banner.png",
					"size": 232
				},
				hero_feature: [{ "title": "Earn" }, { "title": "Redeem" }, { "title": "Repeat" }]
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
				content_title: "Ready to Revolutionize Your Loyalty Rewards?",
				content_description: "At UNLOK, we believe that loyalty rewards should be a catalyst for growth and a driving force behind customer engagement. That's why we've created a platform that empowers businesses like yours to revolutionize their loyalty rewards programs and unlock a world of possibilities.",
				action_button: {
					"url": "/personal",
					"label": "Discover Unlok Rewards"
				},
				content_image: {
					"alt": "Earn with Unlok Rewards",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003811000earn-w-unlok-today%20copy.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003811000earn-w-unlok-today%20copy.svg",
					"size": 10
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
				content_title_1: "Why Choose UNLOK",
				content_title_2: " for Your Loyalty  Rewards",
				content_1: {
					"title": "Stay Ahead of the Curve",
					"description": "Staying ahead of the curve is essential in a rapidly evolving digital landscape. UNLOK equips you with the tools and technologies to adapt to changing customer expectations and market trends. Be at the forefront of innovation and position your business for long-term success."
				},
				content_2: {
					"title": "Unleash the Power of Blockchain",
					"description": "Harness the power of blockchain technology with UNLOK. Our decentralized ecosystem ensures trustless and transparent transactions, providing you and your customers with a secure environment. Say goodbye to data silos and hello to a new era of trust and transparency."
				},
				content_3: {
					"title": "Tap into a Vast Customer Base",
					"description": "By joining UNLOK, you gain access to a thriving community of loyal customers actively seeking rewards. Connect with our user base and expand your reach to unlock new growth opportunities for your business."
				},
				content_4: {
					"title": "Seamless Integration",
					"description": "Transitioning to UNLOK is seamless and hassle-free. Our experienced team will guide you through the integration process, ensuring a smooth transition from your existing rewards program to our robust decentralized ecosystem. Say goodbye to complex migrations and hello to a simplified and efficient process."
				},
				content_5: {
					"title": "Elevate Customer Engagement",
					"description": "UNLOK enhances customer engagement and creates meaningful connections with your audience. With our gamified experience, personalized rewards, and interactive features, you can foster stronger relationships with your customers and keep them coming back for more."
				},
				content_6: {
					"title": "Diversify Your Revenue Streams",
					"description": "UNLOK goes beyond traditional loyalty rewards programs. With our innovative payment facilitator service, UNLOKPAY, you can eliminate transaction charges and streamline payments, creating new revenue streams for your business. Embrace the power of diversified income and maximize your profitability."
				},
				content_image_desktop: {
					"alt": "Business Tree",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687563160000biz-tree-1440.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687563160000biz-tree-1440.svg",
					"size": 1
				},
				content_image_small_desktop: {
					"alt": "Business Tree",
					"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687561433000biz-tree-1024.svg",
					"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1687561433000biz-tree-1024.svg",
					"size": 1
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
				content_tag: "",
				content_title: "Unlock a World of Possibilities with UNLOK's Comprehensive Ecosystem",
				content_paragraph_1: "At UNLOK, we believe in offering more than just traditional rewards. Our platform encompasses a comprehensive ecosystem that empowers merchants like you to explore new horizons and unlock a world of possibilities. Discover the diverse components of our ecosystem designed to elevate your business:",
				content_card: [
					{
						"image": {
							"alt": "UnlokPay",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686002968000UnlokPay%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686002968000UnlokPay%20copy.svg",
							"size": 14
						},
						"title": "UnlokPay",
						"subtitle": "Simplify Payments, Maximize Convenience",
						"description": "Say goodbye to transaction charges and embrace hassle-free payments with UNLOKPAY, our pioneering payment facilitator service. Seamlessly integrate UNLOKPAY into your existing payment infrastructure and provide customers with a seamless and convenient payment experience. Unlock new levels of efficiency while streamlining your business operations."
					},
					{
						"image": {
							"alt": "UnlokMarket",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003002000UnlokMarket%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003002000UnlokMarket%20copy.svg",
							"size": 6
						},
						"title": "UnlokMarket",
						"subtitle": "Expand Your Reach, Tap into the Crypto Market",
						"description": "Explore UNLOKMARKET, our open-market e-commerce platform where products can be bought and sold using cryptocurrencies. Gain exposure to a broader customer base and tap into the growing crypto market. Showcase your products and services, including exclusive NFTs and customized experiences, and connect with crypto enthusiasts looking for unique offerings."
					},
					{
						"image": {
							"alt": "UnlokGC",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003079000UnlokGC%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003079000UnlokGC%20copy.svg",
							"size": 7
						},
						"title": "UnlokGC",
						"subtitle": "Unlock International Discounts with Ease",
						"description": "Got unused gift cards lying around? Trade them for UNLOK tokens or other digital goodies! UNLOKGC lets you exchange your gift cards instantly, so you can treat yourself to something you truly love."
					},
					{
						"image": {
							"alt": "UnlokDebit",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003097000UnlokDebit%20copy.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686003097000UnlokDebit%20copy.svg",
							"size": 5
						},
						"title": "UnlokDebit",
						"subtitle": "Simplify Transactions, Expand Acceptance",
						"description": "Streamline your transactions and enhance global acceptance with UNLOKDEBIT, our secure debit card solution. Consolidate UNLOK tokens and other cryptocurrencies onto a single card, providing your customers with a convenient payment method accepted worldwide. Unlock a seamless payment experience that caters to your customer's needs, regardless of location."
					},
					{
						"image": {
							"alt": "UnlokReward",
							"src": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686760072000unlokreward.svg",
							"url": "https://dcutvpoezjrllqtfzyhv.supabase.co/storage/v1/object/public/images/80af99af-577e-467b-a42c-328f39dc7934/1686760072000unlokreward.svg",
							"size": 9
						},
						"title": "UnlokReward",
						"subtitle": "Elevate Loyalty, Reward Your Customers",
						"description": "Holding UNLOK tokens opens the door to a world of passive rewards through UNLOKREWARD. Delight your customers with discounted airfare, hotel stays, online shop vouchers, and exclusive NFTs. Enhance their loyalty journey and offer them unique and memorable experiences beyond traditional rewards programs."
					}
				]
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
				content_title: "Unlock the Potential of Your Loyalty Rewards with UNLOK",
				content_description: "Unlock the limitless potential of your loyalty rewards program with UNLOK. Join our revolutionary platform and take your business to new heights. Sign up today and discover a world of opportunities waiting for you.",
				action_button: { "url": "/portal", "label": "Get Started" }
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

	component_8 = new Component$9({
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
		}
	};
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$9, safe_not_equal, {});
	}
}

export default Component$a;
