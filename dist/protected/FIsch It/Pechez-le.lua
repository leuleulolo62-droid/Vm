-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = (box.Text:gsub("%s+", "")) -- trim spaces; keep case (work.ink tokens are lowercase)
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'mSRqseqs0VzNYziDmUO0bE5n'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-ElWNRDscIyij
return Vm.run(__src, { name = 'FIsch It/Pechez-le', checksum = 345150343, interval = 2, watermark = 'Y2k-ElWNRDscIyij', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
